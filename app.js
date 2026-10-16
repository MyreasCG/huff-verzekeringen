'use strict';
/* Huff-netwerkanalyse — alle modelberekeningen draaien in de browser op
   voorberekende reistijden (pipeline/05_traveltimes.py). */

// ---------- helpers ----------
const $ = (s, el = document) => el.querySelector(s);
const nf0 = new Intl.NumberFormat('nl-BE', { maximumFractionDigits: 0 });
const nf1 = new Intl.NumberFormat('nl-BE', { maximumFractionDigits: 1, minimumFractionDigits: 1 });
const f0 = v => nf0.format(v);
const f1 = v => nf1.format(v);
const pct = (v, d = 1) => (v * 100).toLocaleString('nl-BE', { maximumFractionDigits: d, minimumFractionDigits: d }) + '%';
const sgn = (v, f) => (v > 0 ? '+' : v < 0 ? '−' : '±') + f(Math.abs(v));
const esc = s => String(s ?? '').replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const ppf = x => { const a = Math.abs(x * 100); return (x > 0 ? '+' : x < 0 ? '−' : '±') + a.toLocaleString('nl-BE', { maximumFractionDigits: a < 0.1 ? 2 : 1, minimumFractionDigits: a < 0.1 ? 2 : 1 }); };
const kfmt = v => Math.abs(v) >= 1e6 ? f1(v / 1e6) + ' mln' : Math.abs(v) >= 1e4 ? f0(v / 1e3) + 'k' : f0(v);

const SEQ = ['#e6ecf4', '#c5d6e5', '#819dc9', '#4f77b3', '#043c93', '#0d1473', '#070b45'];
const DIV = ['#a84300', '#ff934c', '#ffc9a5', '#f2f2f2', '#c5d6e5', '#4f77b3', '#0d1473'];
const CH = { makelaar: '#ff934c', agent: '#2fa595', bank: '#8a6fbf', direct: '#808080' };
const CH_LABEL = { makelaar: 'Makelaar', agent: 'Exclusief agent', bank: 'Bankkantoor', direct: 'Direct kantoor' };
const CH_LIST = ['makelaar', 'agent', 'bank', 'direct'];
const KMX = 70.7, KMY = 111.2; // graden -> km (equirectangulair rond 50,6°N)
const T_MAX = 35;

// ---------- state ----------
let META, SEC, OFF, GEO, PAIRS, NEAR, nS, nO, K, NB, BRANDS;
const TT = {};
let map, REF = null, CUR = null, ucActive = null;
let offMask, offNb, offCh, offPtIdx, offX, offY, secX, secY, munIdx, munList;
const P = { lambda: 1.8, product: 'all', inc: 1, w: { makelaar: 1, agent: 1, bank: 1.2, direct: 0.6 }, multi: 0.1, pt: 0 };
const UI = { brand: 2 }; // standaard Baloise

// ---------- data laden ----------
async function loadAll() {
  const j = u => fetch('data/' + u).then(r => { if (!r.ok) throw new Error(u); return r.json(); });
  const b = u => fetch('data/' + u).then(r => { if (!r.ok) throw new Error(u); return r.arrayBuffer(); });
  setLoading('Sectoren, kantoren en reistijden laden…');
  [META, SEC, OFF, GEO] = await Promise.all([j('meta.json'), j('sectors.json'), j('offices.json'), j('sectors.geojson')]);
  const [pairs, near, tb] = await Promise.all([b('pairs.bin'), b('nearest_brand.bin'), b('tt_base.bin')]);
  PAIRS = new Uint16Array(pairs); NEAR = new Uint8Array(near); TT.base = new Uint8Array(tb);
  BRANDS = META.brands; NB = BRANDS.length; K = META.k; nS = SEC.pop.length; nO = OFF.name.length;
  offMask = Uint16Array.from(OFF.brands);
  offNb = new Uint8Array(nO); offCh = new Uint8Array(nO);
  offX = new Float32Array(nO); offY = new Float32Array(nO); offPtIdx = new Float32Array(nO);
  const ptMax = Math.log1p(quantile(OFF.pt, 0.98));
  for (let j = 0; j < nO; j++) {
    let m = offMask[j], c = 0; while (m) { c += m & 1; m >>= 1; } offNb[j] = c || 1;
    offCh[j] = Math.max(0, CH_LIST.indexOf(OFF.ch[j]));
    offX[j] = OFF.lng[j] * KMX; offY[j] = OFF.lat[j] * KMY;
    offPtIdx[j] = Math.min(1, Math.log1p(OFF.pt[j]) / ptMax);
  }
  secX = new Float32Array(nS); secY = new Float32Array(nS);
  const mm = new Map();
  for (let i = 0; i < nS; i++) {
    secX[i] = SEC.lng[i] * KMX; secY[i] = SEC.lat[i] * KMY;
    const r = SEC.refnis[i]; if (!mm.has(r)) mm.set(r, []); mm.get(r).push(i);
  }
  munIdx = mm; munList = [...mm.keys()];
}
async function scenarioTT(sc) {
  if (!TT[sc]) TT[sc] = new Uint8Array(await fetch(`data/tt_${sc}.bin`).then(r => r.arrayBuffer()));
  return TT[sc];
}
function setLoading(t) { const l = $('#loading'); if (t) { l.hidden = false; $('#loadingText').textContent = t; } else l.hidden = true; }
function quantile(arr, q) { const a = Array.from(arr).filter(Number.isFinite).sort((x, y) => x - y); return a.length ? a[Math.min(a.length - 1, Math.floor(q * (a.length - 1)))] : 0; }
const hasB = (j, b) => (offMask[j] >> b) & 1;

// ---------- Huff-model ----------
function demand() {
  const D = new Float32Array(nS);
  for (let i = 0; i < nS; i++) {
    const a18 = SEC.a18[i], a35 = SEC.a35[i], a65 = SEC.a65[i];
    let seg, eps = P.inc;
    switch (P.product) {
      case 'auto': seg = a18 + a35 + 0.6 * a65; break;
      case 'woning': seg = 0.6 * a18 + a35 + a65; break;
      case 'leven': seg = 0.3 * a18 + a35 + 0.5 * a65; eps = P.inc + 1; break;
      case 'senior': seg = a65 + 0.3 * a35; break;
      default: seg = a18 + a35 + a65;
    }
    D[i] = SEC.pop[i] * seg * Math.pow(SEC.inc[i], eps);
  }
  return D;
}
function attractiveness(closed) {
  const A = new Float32Array(nO);
  for (let j = 0; j < nO; j++) {
    if (closed && closed.has(j)) continue;
    A[j] = P.w[CH_LIST[offCh[j]]] * (1 + P.multi * (offNb[j] - 1)) * (1 + 2 * P.pt * offPtIdx[j]);
  }
  return A;
}
function travelMinutesFrom(lng, lat) {
  // reistijd sector -> willekeurig punt: hemelsbreed x lokale min/km (gekalibreerd op het wegennet)
  const x = lng * KMX, y = lat * KMY, t = new Float32Array(nS).fill(Infinity);
  for (let i = 0; i < nS; i++) {
    const d = Math.hypot(secX[i] - x, secY[i] - y);
    if (d > 45) continue;
    const m = SEC.mpk[i];
    const mpk = d <= 1.5 ? m[0] : d <= 6.5 ? m[0] + (m[1] - m[0]) * (d - 1.5) / 5 : d <= 25 ? m[1] + (m[2] - m[1]) * (d - 6.5) / 18.5 : m[2];
    const tt = Math.max(1, d * mpk);
    if (tt <= T_MAX) t[i] = tt;
  }
  return t;
}
/* opt: {scenario, closed:Set, penalty:Float32Array, virtual:[{lng,lat,brand,ch}]} */
function compute(opt = {}) {
  const tt = TT[opt.scenario || 'base'];
  const A = attractiveness(opt.closed);
  const D = demand();
  const lam = P.lambda, pen = opt.penalty;
  const V = (opt.virtual || []).map(v => ({ ...v, A: P.w[v.ch] * (1 + 2 * P.pt * 0.5), t: v.t || travelMinutesFrom(v.lng, v.lat) }));
  const Pm = new Float32Array(nS * K), Pv = V.map(() => new Float32Array(nS));
  const sumU = new Float32Array(nS), avgT = new Float32Array(nS);
  const share = Array.from({ length: NB }, () => new Float32Array(nS));
  const officeDem = new Float64Array(nO), virtDem = new Float64Array(V.length), brandDem = new Float64Array(NB);
  let totalD = 0;
  for (let i = 0; i < nS; i++) {
    const base = i * K; let s = 0, st = 0;
    for (let k = 0; k < K; k++) {
      const j = PAIRS[base + k]; if (j === 65535) break;
      const q = tt[base + k]; if (q === 255 || A[j] === 0) continue;
      const t = q / 4 + (pen ? pen[j] : 0);
      const u = A[j] * Math.pow(t, -lam); Pm[base + k] = u; s += u; st += u * t;
    }
    for (let v = 0; v < V.length; v++) {
      const t = V[v].t[i]; if (!Number.isFinite(t)) continue;
      const u = V[v].A * Math.pow(t, -lam); Pv[v][i] = u; s += u; st += u * t;
    }
    sumU[i] = s; const Di = D[i]; totalD += Di;
    if (s <= 0) continue;
    avgT[i] = st / s;
    const inv = 1 / s;
    for (let k = 0; k < K; k++) {
      const j = PAIRS[base + k]; if (j === 65535) break;
      const p = Pm[base + k] * inv; if (p === 0) continue;
      Pm[base + k] = p; officeDem[j] += Di * p;
      let m = offMask[j]; const w = p / offNb[j];
      for (let b = 0; m; b++, m >>= 1) if (m & 1) share[b][i] += w;
    }
    for (let v = 0; v < V.length; v++) {
      const p = Pv[v][i] * inv; if (!p) continue;
      Pv[v][i] = p; virtDem[v] += Di * p; share[V[v].brand][i] += p;
    }
  }
  for (let b = 0; b < NB; b++) { let s = 0; const sh = share[b]; for (let i = 0; i < nS; i++) s += D[i] * sh[i]; brandDem[b] = s; }
  return { Pm, Pv, V, sumU, avgT, D, share, officeDem, virtDem, brandDem, totalD, opt };
}
function brandOfficeDem(R, j, b) { return hasB(j, b) ? R.officeDem[j] / offNb[j] : 0; }
function recomputeRef() { REF = compute({ scenario: 'base' }); }

// ---------- kaart ----------
let secClass = new Int8Array(0), offClass = new Int8Array(0), offHl = new Set();
let popup = null;
function initMap() {
  map = new maplibregl.Map({
    container: 'map', style: 'https://basemaps.cartocdn.com/gl/positron-gl-style/style.json',
    bounds: [[2.54, 49.49], [6.41, 51.51]], fitBoundsOptions: { padding: 20 }, attributionControl: { compact: true },
  });
  map.addControl(new maplibregl.NavigationControl({ showCompass: false }), 'top-right');
  map.addControl(new maplibregl.ScaleControl({ unit: 'metric' }), 'bottom-right');
  return new Promise(res => map.on('load', () => {
    const firstSymbol = map.getStyle().layers.find(l => l.type === 'symbol')?.id;
    map.addSource('sectors', { type: 'geojson', data: GEO });
    map.addLayer({
      id: 'sec-fill', type: 'fill', source: 'sectors', paint: {
        'fill-color': classExpr(SEQ), 'fill-opacity': ['case', ['>=', ['coalesce', ['feature-state', 'c'], -1], 0], 0.78, 0],
      },
    }, firstSymbol);
    map.addLayer({ id: 'sec-line', type: 'line', source: 'sectors', minzoom: 10, paint: { 'line-color': '#ffffff', 'line-width': 0.4, 'line-opacity': 0.7 } }, firstSymbol);
    map.addLayer({ id: 'sec-hover', type: 'line', source: 'sectors', paint: { 'line-color': '#0d1473', 'line-width': ['case', ['boolean', ['feature-state', 'hover'], false], 1.6, 0] } }, firstSymbol);

    const feats = [];
    for (let j = 0; j < nO; j++) {
      const props = { ch: OFF.ch[j] };
      for (let b = 0; b < NB; b++) props['b' + b] = hasB(j, b);
      feats.push({ type: 'Feature', id: j, properties: props, geometry: { type: 'Point', coordinates: [OFF.lng[j], OFF.lat[j]] } });
    }
    map.addSource('offices', { type: 'geojson', data: { type: 'FeatureCollection', features: feats } });
    const hl = ['boolean', ['feature-state', 'hl'], false];
    map.addLayer({
      id: 'off', type: 'circle', source: 'offices', paint: {
        'circle-radius': ['interpolate', ['linear'], ['zoom'], 7, ['case', hl, 5, 2], 10, ['case', hl, 8, 3.6], 14, ['case', hl, 12, 7]],
        'circle-color': ['case', ['>=', ['coalesce', ['feature-state', 'c'], -1], 0], classExpr(SEQ, 'c'),
          ['match', ['get', 'ch'], 'makelaar', CH.makelaar, 'agent', CH.agent, 'bank', CH.bank, CH.direct]],
        'circle-stroke-color': ['case', hl, '#0d1473', '#ffffff'], 'circle-stroke-width': ['interpolate', ['linear'], ['zoom'], 7, ['case', hl, 1.5, 0.2], 11, ['case', hl, 2, 0.9]],
        'circle-opacity': ['case', ['boolean', ['feature-state', 'dim'], false], 0.25, 1],
        'circle-stroke-opacity': ['case', ['boolean', ['feature-state', 'dim'], false], 0.25, 1],
      },
    });
    map.addSource('marks', { type: 'geojson', data: fc([]) });
    map.addLayer({ id: 'zone', type: 'fill', source: 'marks', filter: ['==', ['get', 'kind'], 'zone'], paint: { 'fill-color': '#ff934c', 'fill-opacity': 0.12 } });
    map.addLayer({ id: 'zone-line', type: 'line', source: 'marks', filter: ['==', ['get', 'kind'], 'zone'], paint: { 'line-color': '#da5600', 'line-width': 1.5, 'line-dasharray': [3, 2] } });
    map.addLayer({
      id: 'marks-pt', type: 'circle', source: 'marks', filter: ['==', ['geometry-type'], 'Point'], paint: {
        'circle-radius': ['case', ['==', ['get', 'kind'], 'virtual'], 10, 9], 'circle-color': ['case', ['==', ['get', 'kind'], 'virtual'], '#ff934c', '#0d1473'],
        'circle-stroke-color': '#fff', 'circle-stroke-width': 2,
      },
    });
    map.addLayer({ id: 'marks-label', type: 'symbol', source: 'marks', filter: ['has', 'label'], layout: { 'text-field': ['get', 'label'], 'text-size': 11, 'text-font': ['Open Sans Bold'] }, paint: { 'text-color': '#fff' } });
    bindMapEvents();
    res();
  }));
}
function classExpr(ramp, key = 'c') {
  const e = ['match', ['coalesce', ['feature-state', key], -1]];
  ramp.forEach((c, i) => e.push(i, c));
  e.push('rgba(0,0,0,0)');
  return e;
}
const fc = features => ({ type: 'FeatureCollection', features });
function circlePoly(lng, lat, rKm, props) {
  const c = [];
  for (let a = 0; a <= 64; a++) { const t = a / 64 * 2 * Math.PI; c.push([lng + rKm * Math.cos(t) / KMX, lat + rKm * Math.sin(t) / KMY]); }
  return { type: 'Feature', properties: props, geometry: { type: 'Polygon', coordinates: [c] } };
}
function setMarks(features) { map.getSource('marks').setData(fc(features)); }

/* Kleur sectoren. values: Float32Array (NaN = geen kleur). */
let legendState = null, secValues = null, secFmt = f0;
function paintSectors(values, { kind = 'seq', title = '', fmt = f0, breaks = null } = {}) {
  secValues = values; secFmt = fmt;
  const ramp = kind === 'div' ? DIV : SEQ;
  map.setPaintProperty('sec-fill', 'fill-color', classExpr(kind === 'div' ? ramp.map((c, k) => k === 3 ? 'rgba(240,239,236,0.15)' : c) : ramp));
  let br = breaks;
  if (!br) {
    if (kind === 'div') {
      const a = []; for (let i = 0; i < nS; i++) if (Number.isFinite(values[i]) && values[i] !== 0) a.push(Math.abs(values[i]));
      a.sort((x, y) => x - y); const m = a.length ? a[Math.floor(0.95 * (a.length - 1))] : 1;
      br = [-m * 0.6, -m * 0.25, -m * 0.03, m * 0.03, m * 0.25, m * 0.6];
    } else {
      const a = []; for (let i = 0; i < nS; i++) if (Number.isFinite(values[i]) && SEC.pop[i] > 0) a.push(values[i]);
      a.sort((x, y) => x - y);
      br = [1, 2, 3, 4, 5, 6].map(q => a[Math.floor(q / 7 * (a.length - 1))] ?? 0);
    }
  }
  if (secClass.length !== nS) secClass = new Int8Array(nS).fill(-2);
  for (let i = 0; i < nS; i++) {
    const v = values[i];
    let c = -1;
    if (Number.isFinite(v) && (kind === 'div' || v > 0)) { c = 0; while (c < 6 && v >= br[c]) c++; }
    if (secClass[i] !== c) { secClass[i] = c; map.setFeatureState({ source: 'sectors', id: i }, { c }); }
  }
  legendState = { kind, title, fmt, br, ramp };
  renderLegend();
}
function clearSectors() {
  if (secClass.length !== nS) secClass = new Int8Array(nS).fill(-2);
  for (let i = 0; i < nS; i++) if (secClass[i] !== -1) { secClass[i] = -1; map.setFeatureState({ source: 'sectors', id: i }, { c: -1 }); }
  secValues = null; legendState = null; renderLegend();
}
let offLegend = null;
function paintOffices(values, { title = '', fmt = f0, filterBrand = null, only = null } = {}) {
  map.setFilter('off', filterBrand == null ? null : ['==', ['get', 'b' + filterBrand], 1]);
  if (offClass.length !== nO) { offClass = new Int8Array(nO).fill(-2); offDim = new Uint8Array(nO); }
  let br = null;
  if (values) {
    const a = []; for (let j = 0; j < nO; j++) if (Number.isFinite(values[j]) && (!only || only[j])) a.push(values[j]);
    a.sort((x, y) => x - y); br = [1, 2, 3, 4, 5, 6].map(q => a[Math.floor(q / 7 * (a.length - 1))] ?? 0);
  }
  for (let j = 0; j < nO; j++) {
    let c = -1;
    if (values && Number.isFinite(values[j]) && (!only || only[j])) { c = 0; while (c < 6 && values[j] >= br[c]) c++; }
    const dim = !!(only && !only[j]);
    if (offClass[j] !== c || dim !== !!offDim[j]) { offClass[j] = c; offDim[j] = dim ? 1 : 0; map.setFeatureState({ source: 'offices', id: j }, { c, dim }); }
  }
  offLegend = values ? { title, fmt, br } : null;
  renderLegend();
}
let offDim = new Uint8Array(0);
function highlightOffices(set) {
  for (const j of offHl) if (!set.has(j)) map.setFeatureState({ source: 'offices', id: j }, { hl: false });
  for (const j of set) map.setFeatureState({ source: 'offices', id: j }, { hl: true });
  offHl = new Set(set);
}
function renderLegend() {
  const el = $('#legend'); let h = '';
  if (legendState) {
    const { title, fmt, br, ramp, kind } = legendState;
    h += `<div class="lt">${esc(title)}</div><div class="ramp">${ramp.map(c => `<div style="background:${c}"></div>`).join('')}</div>`;
    h += `<div class="ticks"><span>${kind === 'div' ? '−' : ''}</span>${[br[0], br[2], br[3], br[5]].map(v => `<span>${fmt(v)}</span>`).join('')}<span></span></div>`;
  }
  if (offLegend) {
    h += `<div class="lt" style="margin-top:8px">${esc(offLegend.title)}</div><div class="ramp">${SEQ.map(c => `<div style="background:${c}"></div>`).join('')}</div>`;
    h += `<div class="ticks"><span>laag</span><span>${offLegend.fmt(offLegend.br[3])}</span><span>hoog</span></div>`;
  } else {
    h += `<div class="chs">${CH_LIST.map(c => `<span><i class="sw" style="background:${CH[c]}"></i>${CH_LABEL[c]}</span>`).join('')}</div>`;
  }
  el.innerHTML = h; el.hidden = !h;
}

let hoverId = null, mapClickHandler = null;
function bindMapEvents() {
  const tip = $('#tooltip');
  map.on('mousemove', 'sec-fill', e => {
    const f = e.features[0]; if (!f) return;
    if (hoverId !== null) map.setFeatureState({ source: 'sectors', id: hoverId }, { hover: false });
    hoverId = f.id; map.setFeatureState({ source: 'sectors', id: hoverId }, { hover: true });
    const i = f.id; let v = '';
    if (secValues && Number.isFinite(secValues[i])) v = `<br>${esc(legendState?.title || '')}: <b>${secFmt(secValues[i])}</b>`;
    showTip(e.originalEvent, `<b>${esc(SEC.name[i])}</b><br>${esc(SEC.munty[i])} · ${f0(SEC.pop[i])} inwoners${v}`);
  });
  map.on('mouseleave', 'sec-fill', () => { if (hoverId !== null) map.setFeatureState({ source: 'sectors', id: hoverId }, { hover: false }); hoverId = null; tip.hidden = true; });
  map.on('mouseenter', 'off', () => { map.getCanvas().style.cursor = 'pointer'; });
  map.on('mouseleave', 'off', () => { map.getCanvas().style.cursor = ''; });
  map.on('click', e => {
    const fo = map.queryRenderedFeatures(e.point, { layers: ['off'] })[0];
    if (mapClickHandler && mapClickHandler(e, fo ? fo.id : null)) return;
    if (fo) officePopup(fo.id);
  });
}
function showTip(ev, html) { const t = $('#tooltip'); t.innerHTML = html; t.hidden = false; t.style.left = (ev.clientX + 14) + 'px'; t.style.top = (ev.clientY + 14) + 'px'; }
function officePopup(j, extra = '') {
  if (popup) popup.remove();
  const brands = BRANDS.map((b, i) => hasB(j, i) ? `<span class="tag on">${esc(b)}</span>` : '').join('');
  const home = REF ? homeShare(REF, j) : 0;
  popup = new maplibregl.Popup({ maxWidth: '300px' }).setLngLat([OFF.lng[j], OFF.lat[j]]).setHTML(
    `<h4>${esc(OFF.name[j])}</h4><div class="sm">${esc(OFF.street[j])} ${esc(OFF.pc[j])} ${esc(OFF.city[j] || OFF.munty[j])}</div>
     <div style="margin:4px 0">${CH_LABEL[OFF.ch[j]] || OFF.ch[j]} · ${brands}</div>
     <div>Klantpotentieel (Huff): <b>${REF ? f0(REF.officeDem[j]) : '–'}</b> inw.-eq.</div>
     <div>Marktaandeel in eigen sector: <b>${pct(home)}</b></div>
     <div>OV-score: ${f0(OFF.pt[j])} · station op ${f1(OFF.station[j] / 1000)} km</div>${extra}`).addTo(map);
}
function homeShare(R, j) { const i = OFF.sector[j], base = i * K; for (let k = 0; k < K; k++) if (PAIRS[base + k] === j) return R.Pm[base + k]; return 0; }
function flyToOffice(j) { map.flyTo({ center: [OFF.lng[j], OFF.lat[j]], zoom: Math.max(map.getZoom(), 12) }); officePopup(j); }
function flyToSectors(idx) {
  let a = 180, b = 90, c = -180, d = -90;
  for (const i of idx) { a = Math.min(a, SEC.lng[i]); b = Math.min(b, SEC.lat[i]); c = Math.max(c, SEC.lng[i]); d = Math.max(d, SEC.lat[i]); }
  map.fitBounds([[a - 0.02, b - 0.015], [c + 0.02, d + 0.015]], { padding: 40, maxZoom: 13 });
}
function hint(t) { const h = $('#maphint'); h.hidden = !t; if (t) h.textContent = t; }

// ---------- UI-bouwstenen ----------
function brandSelect(id = 'ucBrand', label = 'Merk / maatschappij') {
  return `<label>${label}<select id="${id}">${BRANDS.map((b, i) => `<option value="${i}" ${i === UI.brand ? 'selected' : ''}>${esc(b)}</option>`).join('')}</select></label>`;
}
function tiles(items) {
  return `<div class="tiles">${items.map(t => `<div class="tile"><div class="v">${t.v}</div><div class="l">${t.l}</div>${t.d ? `<div class="dlt ${t.dc || ''}">${t.d}</div>` : ''}</div>`).join('')}</div>`;
}
/* Horizontale staafgrafiek (SVG). items: [{label, value, hl, tip}] */
function hbar(items, { fmt = f0, diverging = false, color = '#0d1473' } = {}) {
  const W = 380, rowH = 22, lw = 92, vw = 62, H = items.length * rowH + 4;
  const max = Math.max(1e-9, ...items.map(d => Math.abs(d.value)));
  const plotW = W - lw - vw - 8;
  const zero = diverging ? lw + plotW / 2 : lw;
  const scale = diverging ? plotW / 2 / max : plotW / max;
  let s = `<svg class="bars" viewBox="0 0 ${W} ${H}" role="img">`;
  if (diverging) s += `<line x1="${zero}" x2="${zero}" y1="0" y2="${H}" stroke="#b3b3b3"/>`;
  items.forEach((d, k) => {
    const y = k * rowH + 3, w = Math.max(1, Math.abs(d.value) * scale);
    const x = d.value < 0 ? zero - w : zero;
    const fill = diverging ? (d.value < 0 ? '#ff934c' : '#0d1473') : (d.hl === false ? '#c5d6e5' : color);
    const tipTxt = esc(d.tip || `${d.label}: ${fmt(d.value)}`);
    s += `<text x="${lw - 6}" y="${y + 13}" text-anchor="end">${esc(d.label)}</text>`;
    s += `<rect class="bar" data-tip="${tipTxt}" x="${x}" y="${y + 2}" width="${w}" height="${rowH - 8}" rx="3" fill="${fill}"/>`;
    s += `<text class="val" x="${W - 2}" y="${y + 13}" text-anchor="end">${fmt(d.value)}</text>`;
  });
  return s + '</svg>';
}
document.addEventListener('mouseover', e => {
  const t = e.target.closest && e.target.closest('[data-tip]');
  if (t) showTip(e, t.getAttribute('data-tip'));
});
document.addEventListener('mousemove', e => { const t = e.target.closest && e.target.closest('[data-tip]'); if (t) showTip(e, t.getAttribute('data-tip')); });
document.addEventListener('mouseout', e => { if (e.target.closest && e.target.closest('[data-tip]')) $('#tooltip').hidden = true; });

function officeRow(j, cols) {
  return `<tr data-o="${j}"><td><b>${esc(OFF.name[j])}</b><div class="sm">${esc(OFF.munty[j])} · ${CH_LABEL[OFF.ch[j]] || ''}</div></td>${cols.map(c => `<td class="n">${c}</td>`).join('')}</tr>`;
}
function bindOfficeRows(root) {
  root.querySelectorAll('tr[data-o]').forEach(tr => tr.addEventListener('click', () => {
    root.querySelectorAll('tr.sel').forEach(x => x.classList.remove('sel')); tr.classList.add('sel');
    const j = +tr.dataset.o; if (ucActive?.onOffice) ucActive.onOffice(j); else flyToOffice(j);
  }));
}
function bindMunRows(root) {
  root.querySelectorAll('tr[data-m]').forEach(tr => tr.addEventListener('click', () => {
    root.querySelectorAll('tr.sel').forEach(x => x.classList.remove('sel')); tr.classList.add('sel');
    flyToSectors(munIdx.get(tr.dataset.m));
  }));
}
function munAgg(fn) {
  // fn(i) -> object met optelbare velden; geeft per gemeente de som
  return munList.map(r => { const acc = { refnis: r, name: SEC.munty[munIdx.get(r)[0]], prov: SEC.prov[munIdx.get(r)[0]] }; for (const i of munIdx.get(r)) { const o = fn(i); for (const k in o) acc[k] = (acc[k] || 0) + o[k]; } return acc; });
}
function brandTags(j) { return BRANDS.map((b, i) => hasB(j, i) ? `<span class="tag">${esc(b)}</span>` : '').join(''); }
function nearestBrandMinutes(b, i) { const q = NEAR[b * nS + i]; return q === 255 ? Infinity : q / 4; }

// ---------- Use cases ----------
const UC = [];
const reg = uc => UC.push(uc);

reg({
  id: 'share', group: 'Positie', title: 'Marktaandeel & verzorgingsgebied', desc: 'Huff-marktaandeel per merk en sector',
  render(el) {
    el.innerHTML = `<h2>Marktaandeel & verzorgingsgebied</h2>
      <p class="lead">Kans dat een inwoner van een sector bij een kantoor van het gekozen merk terechtkomt (Huff). Multi-merk makelaars verdelen hun aandeel gelijk over hun maatschappijen.</p>
      <div class="controls">${brandSelect()}</div><div id="out"></div>`;
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.update(); };
  },
  update() {
    const b = UI.brand, R = REF, nat = R.brandDem[b] / R.totalD;
    paintSectors(R.share[b], { title: `Marktaandeel ${BRANDS[b]}`, fmt: v => pct(v, 0) });
    paintOffices(null, { filterBrand: b });
    let cnt = 0; for (let j = 0; j < nO; j++) cnt += hasB(j, b);
    let wt = 0, ws = 0; for (let i = 0; i < nS; i++) { const t = nearestBrandMinutes(b, i); ws += SEC.pop[i]; wt += SEC.pop[i] * Math.min(t, T_MAX); }
    const all = BRANDS.map((n, k) => ({ label: n, value: R.brandDem[k] / R.totalD, hl: k === b })).sort((x, y) => y.value - x.value);
    const prov = {};
    for (let i = 0; i < nS; i++) { const p = SEC.prov[i]; (prov[p] ||= { d: 0, s: 0, pop: 0 }); prov[p].d += R.D[i]; prov[p].s += R.D[i] * R.share[b][i]; prov[p].pop += SEC.pop[i]; }
    const pc = {}; for (let j = 0; j < nO; j++) if (hasB(j, b)) pc[OFF.prov[j]] = (pc[OFF.prov[j]] || 0) + 1;
    const rows = Object.entries(prov).sort((x, y) => y[1].s / y[1].d - x[1].s / x[1].d);
    $('#out').innerHTML = tiles([
      { v: pct(nat), l: `Nationaal Huff-aandeel ${esc(BRANDS[b])}` },
      { v: f0(cnt), l: 'Verkooppunten (kantoren met dit merk)' },
      { v: kfmt(R.brandDem[b]), l: 'Klantpotentieel (inwoner-equivalenten)' },
      { v: f1(wt / ws) + ' min', l: 'Gem. rijtijd tot dichtstbijzijnd kantoor' },
    ]) + `<h3>Aandeel per merk (nationaal)</h3>${hbar(all, { fmt: v => pct(v) })}
      <h3>Per provincie</h3><table><thead><tr><th>Provincie</th><th class="n">Aandeel</th><th class="n">Kantoren</th><th class="n">Inw. per kantoor</th></tr></thead><tbody>
      ${rows.map(([p, o]) => `<tr><td>${esc(p)}</td><td class="n">${pct(o.s / o.d)}</td><td class="n">${f0(pc[p] || 0)}</td><td class="n">${pc[p] ? f0(o.pop / pc[p]) : '–'}</td></tr>`).join('')}</tbody></table>`;
  },
});

reg({
  id: 'gaps', group: 'Positie', title: 'Onderbediende gebieden', desc: 'Onbenut potentieel en lange rijtijden',
  render(el) {
    el.innerHTML = `<h2>Onderbediende gebieden</h2>
      <p class="lead"><b>Onbenut potentieel</b> = klantpotentieel × (nationaal aandeel − lokaal aandeel). Zo zie je waar het merk minder klanten bereikt dan zijn nationale gemiddelde, rekening houdend met concurrentie en bereikbaarheid. Op de kaart zijn lichte of lege zones goed bediend; hoe donkerder, hoe groter het tekort.</p>
      <div class="controls">${brandSelect()}
        <label>Kaartlaag<select id="gMetric"><option value="gap">Onbenut potentieel</option><option value="time">Rijtijd tot dichtstbijzijnd kantoor</option><option value="share">Lokaal aandeel t.o.v. nationaal</option></select></label></div>
      <div class="btnrow"><button class="btn small" id="toSite">Zoek de beste nieuwe locaties →</button></div><div id="out"></div>`;
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.update(); };
    $('#gMetric').onchange = () => this.update();
    $('#toSite').onclick = () => activate('site');
  },
  update() {
    const b = UI.brand, R = REF, nat = R.brandDem[b] / R.totalD, metric = $('#gMetric').value;
    const gap = new Float32Array(nS);
    for (let i = 0; i < nS; i++) gap[i] = R.D[i] * Math.max(0, nat - R.share[b][i]);
    if (metric === 'gap') paintSectors(gap, { title: `Onbenut potentieel ${BRANDS[b]} (inw.-eq.)`, fmt: f0 });
    else if (metric === 'time') {
      const t = new Float32Array(nS); for (let i = 0; i < nS; i++) t[i] = Math.min(nearestBrandMinutes(b, i), T_MAX);
      paintSectors(t, { title: `Rijtijd tot dichtstbijzijnd ${BRANDS[b]}-kantoor (min)`, fmt: v => f0(v) + "'", breaks: [3, 5, 8, 12, 16, 22] });
    } else {
      const r = new Float32Array(nS); for (let i = 0; i < nS; i++) r[i] = R.D[i] > 0 ? R.share[b][i] / nat - 1 : NaN;
      paintSectors(r, { kind: 'div', title: `Lokaal aandeel t.o.v. nationaal`, fmt: v => sgn(v, x => pct(x, 0)), breaks: [-0.6, -0.3, -0.08, 0.08, 0.3, 0.6] });
    }
    paintOffices(null, { filterBrand: b });
    const mun = munAgg(i => ({ gap: gap[i], d: R.D[i], s: R.D[i] * R.share[b][i], pop: SEC.pop[i], tp: SEC.pop[i] * Math.min(nearestBrandMinutes(b, i), T_MAX) }));
    const oc = {}; for (let j = 0; j < nO; j++) if (hasB(j, b)) { const r = SEC.refnis[OFF.sector[j]]; oc[r] = (oc[r] || 0) + 1; }
    mun.sort((x, y) => y.gap - x.gap);
    let totalGap = 0; for (let i = 0; i < nS; i++) totalGap += gap[i];
    let far = 0; for (let i = 0; i < nS; i++) if (nearestBrandMinutes(b, i) > 10) far += SEC.pop[i];
    const zero = mun.filter(m => !oc[m.refnis] && m.pop > 5000).length;
    $('#out').innerHTML = tiles([
      { v: kfmt(totalGap), l: 'Totaal onbenut potentieel (inw.-eq.)' },
      { v: kfmt(far), l: 'Inwoners > 10 min van een kantoor' },
      { v: f0(zero), l: 'Gemeenten (>5.000 inw.) zonder kantoor' },
      { v: pct(nat), l: 'Nationaal referentie-aandeel' },
    ]) + `<h3>Top 30 gemeenten met onbenut potentieel</h3><table><thead><tr><th>Gemeente</th><th class="n">Potentieel</th><th class="n">Aandeel</th><th class="n">Rijtijd</th><th class="n">Kant.</th></tr></thead><tbody>
      ${mun.slice(0, 30).map(m => `<tr data-m="${m.refnis}"><td><b>${esc(m.name)}</b><div class="sm">${esc(m.prov)} · ${f0(m.pop)} inw.</div></td><td class="n">${f0(m.gap)}</td><td class="n">${pct(m.s / m.d)}</td><td class="n">${f1(m.tp / m.pop)}'</td><td class="n">${oc[m.refnis] || 0}</td></tr>`).join('')}</tbody></table>`;
    bindMunRows($('#out'));
  },
});

reg({
  id: 'cannibal', group: 'Netwerk', title: 'Kannibalisatie-analyse', desc: 'Overlap tussen kantoren van hetzelfde merk',
  render(el) {
    el.innerHTML = `<h2>Kannibalisatie</h2>
      <p class="lead">Per kantoor: welk deel van zijn klantpotentieel voor dit merk blijft binnen het merk als het kantoor zou sluiten (Huff-herverdeling)? Een <b>index van 100%</b> betekent dat het merk niets verliest, want de klanten vinden een ander verkooppunt van hetzelfde merk: volledige kannibalisatie. De <b>netto bijdrage</b> is wat het merk werkelijk verliest bij sluiting.</p>
      <div class="controls">${brandSelect()}</div><div id="focus"></div><div id="out"></div>`;
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.focus = null; this.update(); };
  },
  stats() {
    const b = UI.brand, R = REF, C = new Float64Array(nO), Rt = new Float64Array(nO);
    for (let i = 0; i < nS; i++) {
      const base = i * K, S = R.share[b][i], Di = R.D[i]; if (!Di) continue;
      for (let k = 0; k < K; k++) {
        const j = PAIRS[base + k]; if (j === 65535) break; if (!hasB(j, b)) continue;
        const p = R.Pm[base + k]; if (!p) continue;
        const sj = 1 / offNb[j], F = Di * p;
        C[j] += F * sj; Rt[j] += F * Math.max(0, (S - p * sj) / Math.max(1e-6, 1 - p));
      }
    }
    const idx = new Float32Array(nO).fill(NaN);
    for (let j = 0; j < nO; j++) if (hasB(j, b) && C[j] > 0) idx[j] = Math.min(1, Rt[j] / C[j]);
    return { C, idx };
  },
  update() {
    const b = UI.brand; const { C, idx } = this.stats(); this.C = C; this.idx = idx;
    const only = new Uint8Array(nO); for (let j = 0; j < nO; j++) only[j] = hasB(j, b);
    if (this.focus != null) return this.showFocus(this.focus);
    const dens = new Float32Array(nS);
    for (let i = 0; i < nS; i++) { const base = i * K; let n = 0; for (let k = 0; k < K; k++) { const j = PAIRS[base + k]; if (j === 65535) break; if (TT.base[base + k] <= 40 && hasB(j, b)) n++; } dens[i] = n; }
    paintSectors(dens, { title: `Aantal ${BRANDS[b]}-kantoren binnen 10 min`, fmt: f0, breaks: [1, 2, 3, 5, 8, 12] });
    paintOffices(idx, { title: 'Kannibalisatie-index kantoor', fmt: v => pct(v, 0), filterBrand: b, only });
    highlightOffices(new Set());
    const list = []; for (let j = 0; j < nO; j++) if (Number.isFinite(idx[j])) list.push(j);
    let wsum = 0, cs = 0; for (const j of list) { wsum += C[j]; cs += C[j] * idx[j]; }
    list.sort((x, y) => idx[y] * C[y] - idx[x] * C[x]);
    const hi = list.filter(j => idx[j] > 0.6).length;
    $('#focus').innerHTML = '';
    $('#out').innerHTML = tiles([
      { v: pct(cs / wsum), l: 'Gewogen kannibalisatie-index netwerk' },
      { v: f0(hi), l: 'Kantoren met index > 60%' },
      { v: f0(list.length), l: `Kantoren met ${esc(BRANDS[b])}` },
      { v: f0(wsum / list.length), l: 'Gem. merkpotentieel per kantoor' },
    ]) + `<h3>Sterkste overlap (index × volume)</h3><p class="sm">Klik een kantoor voor zijn verzorgingsgebied en waar zijn klanten heen zouden gaan.</p>
      <table><thead><tr><th>Kantoor</th><th class="n">Merkpot.</th><th class="n">Netto</th><th class="n">Index</th></tr></thead><tbody>${list.slice(0, 40).map(j => officeRow(j, [f0(C[j]), f0(C[j] * (1 - idx[j])), pct(idx[j], 0)])).join('')}</tbody></table>`;
    bindOfficeRows($('#out'));
  },
  onOffice(j) { if (!hasB(j, UI.brand)) { flyToOffice(j); return; } this.focus = j; this.showFocus(j); },
  showFocus(j) {
    const b = UI.brand, R = REF, catchV = new Float32Array(nS).fill(NaN), div = new Map();
    for (let i = 0; i < nS; i++) {
      const base = i * K; let pj = 0, kj = -1;
      for (let k = 0; k < K; k++) { const o = PAIRS[base + k]; if (o === 65535) break; if (o === j) { pj = R.Pm[base + k]; kj = k; break; } }
      if (kj < 0 || !pj) continue;
      catchV[i] = pj;
      const F = R.D[i] * pj;
      for (let k = 0; k < K; k++) { const o = PAIRS[base + k]; if (o === 65535) break; if (k === kj) continue; const p = R.Pm[base + k]; if (p) div.set(o, (div.get(o) || 0) + F * p / (1 - pj)); }
    }
    paintSectors(catchV, { title: `Kans dat inwoners voor ${OFF.name[j]} kiezen`, fmt: v => pct(v, 0), breaks: [0.02, 0.05, 0.1, 0.2, 0.3, 0.5] });
    const top = [...div.entries()].sort((x, y) => y[1] - x[1]).slice(0, 12);
    const tot = [...div.values()].reduce((a, c) => a + c, 0);
    const own = [...div.entries()].reduce((a, [o, v]) => a + (hasB(o, b) ? v / offNb[o] : 0), 0);
    highlightOffices(new Set([j, ...top.map(t => t[0])]));
    flyToOffice(j);
    $('#focus').innerHTML = `<div class="note"><b>${esc(OFF.name[j])}</b> (${esc(OFF.munty[j])}): kannibalisatie-index <b>${pct(this.idx[j], 0)}</b>.
      Bij sluiting gaat ${pct(own / tot, 0)} van zijn klantenstroom naar andere ${esc(BRANDS[b])}-verkooppunten.
      <div class="btnrow"><button class="btn small" id="backList">← Terug naar overzicht</button></div></div>
      <h3>Waar gaan zijn klanten heen bij sluiting?</h3><table><thead><tr><th>Kantoor</th><th class="n">Instroom</th><th class="n">Aandeel</th></tr></thead><tbody>
      ${top.map(([o, v]) => `<tr data-o="${o}"><td><b>${esc(OFF.name[o])}</b><div class="sm">${esc(OFF.munty[o])} · ${brandTags(o)}</div></td><td class="n">${f0(v)}</td><td class="n">${pct(v / tot, 0)}</td></tr>`).join('')}</tbody></table>`;
    $('#out').innerHTML = '';
    $('#backList').onclick = () => { this.focus = null; this.update(); };
    $('#focus').querySelectorAll('tr[data-o]').forEach(tr => tr.onclick = () => flyToOffice(+tr.dataset.o));
  },
  leave() { this.focus = null; },
});

const LEZ = {
  none: null,
  antwerpen: { lng: 4.4025, lat: 51.2194, r: 4.5, label: 'LEZ Antwerpen (benadering)' },
  gent: { lng: 3.7250, lat: 51.0543, r: 2.3, label: 'LEZ Gent (binnen R40, benadering)' },
  brussel: { lng: 4.3700, lat: 50.8380, r: 7.0, label: 'LEZ Brussel (gewest, benadering)' },
};
reg({
  id: 'mobility', group: 'Scenario’s', title: 'Impact van mobiliteitsingrepen', desc: 'Afsluitingen, spits, zone 30, LEZ, werven',
  render(el) {
    el.innerHTML = `<h2>Mobiliteitsingrepen</h2>
      <p class="lead">Herberekende rijtijden op het OSM-wegennet (scenario's) en/of een tijdsstraf voor kantoren in een zone, zoals een LEZ, parkeerbeleid of een werf. Vergelijking met de basistoestand.</p>
      <div class="controls">
        <label>Netwerkscenario<select id="mSc">${Object.entries(META.scenarios).map(([k, v]) => `<option value="${k}" ${k === (this.sc || 'kennedy') ? 'selected' : ''}>${esc(v)}</option>`).join('')}</select></label>
        <label>Zone-ingreep<select id="mZone"><option value="none">Geen</option><option value="antwerpen">LEZ Antwerpen</option><option value="gent">LEZ Gent</option><option value="brussel">LEZ Brussel</option><option value="custom">Eigen zone (klik op kaart)</option></select></label>
        <label>Straal (km)<input type="number" id="mR" value="3" min="0.5" max="20" step="0.5" style="width:70px"></label>
        <label>Extra minuten<input type="number" id="mMin" value="6" min="0" max="30" step="1" style="width:70px"></label>
        ${brandSelect('mBrand', 'Focus merk')}
        <label>Kaartlaag<select id="mLayer"><option value="share">Δ marktaandeel merk</option><option value="time">Δ gem. rijtijd naar gekozen kantoor</option></select></label>
      </div><div id="out"></div>`;
    ['mSc', 'mZone', 'mR', 'mMin', 'mLayer'].forEach(id => $('#' + id).onchange = () => this.update());
    $('#mBrand').onchange = e => { UI.brand = +e.target.value; this.update(); };
    $('#mZone').addEventListener('change', e => { const z = LEZ[e.target.value]; if (z) { $('#mR').value = z.r; this.zone = { lng: z.lng, lat: z.lat }; } });
    mapClickHandler = e => { if ($('#mZone').value !== 'custom') return false; this.zone = { lng: e.lngLat.lng, lat: e.lngLat.lat }; this.update(); return true; };
  },
  async update() {
    const sc = $('#mSc').value; this.sc = sc; const zsel = $('#mZone').value, b = UI.brand;
    if (!TT[sc]) { setLoading('Scenario laden…'); await scenarioTT(sc); setLoading(null); }
    let pen = null, zoneTxt = '';
    if (zsel !== 'none') {
      if (zsel !== 'custom') this.zone = { lng: LEZ[zsel].lng, lat: LEZ[zsel].lat };
      hint(zsel === 'custom' ? 'Klik op de kaart om het middelpunt van de zone te kiezen' : null);
      if (this.zone) {
        const r = +$('#mR').value, add = +$('#mMin').value, zx = this.zone.lng * KMX, zy = this.zone.lat * KMY;
        pen = new Float32Array(nO); let n = 0;
        for (let j = 0; j < nO; j++) if (Math.hypot(offX[j] - zx, offY[j] - zy) <= r) { pen[j] = add; n++; }
        setMarks([circlePoly(this.zone.lng, this.zone.lat, r, { kind: 'zone' })]);
        zoneTxt = `${n} kantoren in de zone krijgen +${add} min`;
      }
    } else { setMarks([]); hint(null); }
    CUR = compute({ scenario: sc, penalty: pen });
    const R = REF;
    const layer = $('#mLayer').value;
    const v = new Float32Array(nS);
    if (layer === 'share') for (let i = 0; i < nS; i++) v[i] = CUR.share[b][i] - R.share[b][i];
    else for (let i = 0; i < nS; i++) v[i] = CUR.avgT[i] - R.avgT[i];
    if (layer === 'share') paintSectors(v, { kind: 'div', title: `Δ marktaandeel ${BRANDS[b]} (procentpunt)`, fmt: ppf });
    else { for (let i = 0; i < nS; i++) v[i] = -v[i]; paintSectors(v, { kind: 'div', title: 'Rijtijdwinst (+) of -verlies (−) in min', fmt: x => sgn(x, f1) }); }
    paintOffices(null, { filterBrand: b });
    let tR = 0, tC = 0, dsum = 0; for (let i = 0; i < nS; i++) { tR += R.D[i] * R.avgT[i]; tC += CUR.D[i] * CUR.avgT[i]; dsum += R.D[i]; }
    const bd = BRANDS.map((n, k) => ({ label: n, value: CUR.brandDem[k] - R.brandDem[k], tip: `${n}: ${sgn(CUR.brandDem[k] - R.brandDem[k], f0)} inw.-eq. (${sgn((CUR.brandDem[k] / R.brandDem[k] - 1) * 100, f1)}%)` })).sort((x, y) => y.value - x.value);
    const delta = []; for (let j = 0; j < nO; j++) { const d = CUR.officeDem[j] - R.officeDem[j]; if (Math.abs(d) > 0.5) delta.push([j, d]); }
    delta.sort((x, y) => x[1] - y[1]);
    const losers = delta.slice(0, 12), winners = delta.slice(-8).reverse();
    let moved = 0; for (const [, d] of delta) if (d > 0) moved += d;
    $('#out').innerHTML = (zoneTxt ? `<div class="note">${esc(zoneTxt)}${zsel !== 'custom' && zsel !== 'none' ? ' · ' + esc(LEZ[zsel].label) : ''}</div>` : '') + tiles([
      { v: f1(tC / dsum) + ' min', l: 'Gem. rijtijd klant → gekozen kantoor', d: sgn(tC / dsum - tR / dsum, f1) + ' min t.o.v. basis', dc: tC > tR ? 'neg' : 'pos' },
      { v: kfmt(moved), l: 'Klantpotentieel dat van kantoor wisselt' },
      { v: sgn(CUR.brandDem[b] - R.brandDem[b], kfmt), l: `Effect op ${esc(BRANDS[b])} (inw.-eq.)` },
      { v: f0(delta.length), l: 'Kantoren met wijziging' },
    ]) + `<h3>Effect per merk</h3>${hbar(bd, { fmt: x => sgn(x, kfmt), diverging: true })}
      <h3>Grootste verliezers</h3><table><thead><tr><th>Kantoor</th><th class="n">Δ potentieel</th><th class="n">%</th></tr></thead><tbody>${losers.map(([j, d]) => officeRow(j, [sgn(d, f0), sgn(d / R.officeDem[j] * 100, f1) + '%'])).join('')}</tbody></table>
      <h3>Grootste winnaars</h3><table><thead><tr><th>Kantoor</th><th class="n">Δ potentieel</th><th class="n">%</th></tr></thead><tbody>${winners.map(([j, d]) => officeRow(j, [sgn(d, f0), sgn(d / R.officeDem[j] * 100, f1) + '%'])).join('')}</tbody></table>`;
    bindOfficeRows($('#out'));
  },
  leave() { setMarks([]); hint(null); mapClickHandler = null; },
});

reg({
  id: 'site', group: 'Scenario’s', title: 'Nieuwe vestiging simuleren', desc: 'Klik een locatie of laat het model zoeken',
  render(el) {
    el.innerHTML = `<h2>Nieuwe vestiging</h2>
      <p class="lead">Klik op de kaart om een kantoor toe te voegen. Je ziet de extra klanten, hoeveel daarvan van eigen kantoren komen (kannibalisatie) en hoeveel van concurrenten. Of laat het model de 10 beste locaties zoeken.</p>
      <div class="controls">${brandSelect()}
        <label>Kanaal<select id="sCh"><option value="makelaar">Makelaar</option><option value="agent">Exclusief agent</option><option value="bank">Bankkantoor</option></select></label></div>
      <div class="btnrow"><button class="btn primary" id="sFind">Zoek top-10 locaties</button><button class="btn" id="sClear">Wissen</button></div><div id="out"></div>`;
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.cands = null; this.update(); };
    $('#sCh').onchange = () => this.update();
    $('#sFind').onclick = () => this.find();
    $('#sClear').onclick = () => { this.site = null; this.cands = null; this.update(); };
    hint('Klik op de kaart om een nieuw kantoor te plaatsen');
    mapClickHandler = e => { this.site = { lng: e.lngLat.lng, lat: e.lngLat.lat }; this.update(); return true; };
  },
  find() {
    const b = UI.brand, R = REF, nat = R.brandDem[b] / R.totalD, A = P.w[$('#sCh').value], lam = P.lambda;
    const cand = [];
    for (let i = 0; i < nS; i++) if (SEC.pop[i] > 200 && nearestBrandMinutes(b, i) > 3) cand.push([i, R.D[i] * Math.max(0, nat - R.share[b][i])]);
    cand.sort((x, y) => y[1] - x[1]);
    const pool = cand.slice(0, 500).map(c => c[0]), res = [];
    for (const c of pool) {
      const cx = secX[c], cy = secY[c]; let gain = 0;
      for (let i = 0; i < nS; i++) {
        const d = Math.hypot(secX[i] - cx, secY[i] - cy); if (d > 30) continue;
        const m = SEC.mpk[i], mpk = d <= 1.5 ? m[0] : d <= 6.5 ? m[0] + (m[1] - m[0]) * (d - 1.5) / 5 : d <= 25 ? m[1] + (m[2] - m[1]) * (d - 6.5) / 18.5 : m[2];
        const t = Math.max(1, d * mpk); if (t > T_MAX) continue;
        const S = R.sumU[i]; if (!S) continue;
        const Uc = A * Math.pow(t, -lam), Ub = R.share[b][i] * S;
        gain += R.D[i] * ((Ub + Uc) / (S + Uc) - Ub / S);
      }
      res.push([c, gain]);
    }
    res.sort((x, y) => y[1] - x[1]);
    const pick = [];
    for (const r of res) { if (pick.every(p => Math.hypot(secX[p[0]] - secX[r[0]], secY[p[0]] - secY[r[0]]) > 8)) pick.push(r); if (pick.length === 10) break; }
    this.cands = pick; this.site = null; this.update();
    flyToSectors(pick.map(p => p[0]));
  },
  update() {
    const b = UI.brand, ch = $('#sCh').value, R = REF;
    const marks = (this.cands || []).map((c, k) => ({ type: 'Feature', properties: { kind: 'cand', label: String(k + 1) }, geometry: { type: 'Point', coordinates: [SEC.lng[c[0]], SEC.lat[c[0]]] } }));
    paintOffices(null, { filterBrand: b });
    let html = '';
    if (this.site) {
      marks.push({ type: 'Feature', properties: { kind: 'virtual', label: '+' }, geometry: { type: 'Point', coordinates: [this.site.lng, this.site.lat] } });
      CUR = compute({ virtual: [{ ...this.site, brand: b, ch }] });
      const gainBrand = CUR.brandDem[b] - R.brandDem[b], newDem = CUR.virtDem[0];
      let own = 0; for (let j = 0; j < nO; j++) if (hasB(j, b)) own += (R.officeDem[j] - CUR.officeDem[j]) / offNb[j];
      const comp = BRANDS.map((n, k) => ({ label: n, value: CUR.brandDem[k] - R.brandDem[k] })).filter(d => d.value < -0.5 || d.label === BRANDS[b]).sort((x, y) => x.value - y.value);
      paintSectors(CUR.Pv[0], { title: 'Kans dat inwoners het nieuwe kantoor kiezen', fmt: v => pct(v, 0), breaks: [0.02, 0.05, 0.1, 0.2, 0.3, 0.5] });
      const losers = []; for (let j = 0; j < nO; j++) { const d = CUR.officeDem[j] - R.officeDem[j]; if (d < -1) losers.push([j, d]); }
      losers.sort((x, y) => x[1] - y[1]);
      html += tiles([
        { v: f0(newDem), l: 'Klantpotentieel nieuw kantoor' },
        { v: sgn(gainBrand, f0), l: `Netto winst ${esc(BRANDS[b])}` },
        { v: pct(own / newDem, 0), l: 'Kannibalisatie (van eigen kantoren)' },
        { v: pct(1 - own / newDem, 0), l: 'Gewonnen van concurrenten' },
      ]) + `<h3>Verschuiving per merk</h3>${hbar(comp, { fmt: x => sgn(x, f0), diverging: true })}
        <h3>Meest getroffen bestaande kantoren</h3><table><thead><tr><th>Kantoor</th><th class="n">Δ potentieel</th></tr></thead><tbody>${losers.slice(0, 10).map(([j, d]) => officeRow(j, [sgn(d, f0)])).join('')}</tbody></table>`;
    } else {
      clearSectors(); CUR = null;
      const nat = R.brandDem[b] / R.totalD, gap = new Float32Array(nS);
      for (let i = 0; i < nS; i++) gap[i] = R.D[i] * Math.max(0, nat - R.share[b][i]);
      paintSectors(gap, { title: `Onbenut potentieel ${BRANDS[b]} (context)`, fmt: f0 });
    }
    if (this.cands) {
      html += `<h3>Top-10 voorgestelde locaties</h3><p class="sm">Greedy zoektocht over 500 sectoren met het grootste onbenutte potentieel, minstens 8 km uit elkaar, bruto winst voor het merk.</p>
        <table><thead><tr><th>#</th><th>Sector</th><th class="n">Winst merk</th></tr></thead><tbody>${this.cands.map((c, k) => `<tr data-c="${k}"><td>${k + 1}</td><td><b>${esc(SEC.name[c[0]])}</b><div class="sm">${esc(SEC.munty[c[0]])}</div></td><td class="n">${f0(c[1])}</td></tr>`).join('')}</tbody></table>`;
    }
    setMarks(marks);
    $('#out').innerHTML = html || '<p class="sm">Nog geen locatie gekozen.</p>';
    bindOfficeRows($('#out'));
    $('#out').querySelectorAll('tr[data-c]').forEach(tr => tr.onclick = () => { const c = this.cands[+tr.dataset.c][0]; this.site = { lng: SEC.lng[c], lat: SEC.lat[c] }; this.update(); map.flyTo({ center: [SEC.lng[c], SEC.lat[c]], zoom: 11 }); });
  },
  leave() { setMarks([]); hint(null); mapClickHandler = null; },
});

reg({
  id: 'closure', group: 'Scenario’s', title: 'Sluiting & consolidatie', desc: 'Welke klanten blijven bij het merk?',
  render(el) {
    this.closed = this.closed || new Set();
    el.innerHTML = `<h2>Sluiting & consolidatie</h2>
      <p class="lead">Sluit kantoren (klik ze aan op de kaart) of laat de kantoren met het kleinste verzorgingsgebied wegvallen. Het model toont hoeveel klantpotentieel binnen het merk blijft.</p>
      <div class="controls">${brandSelect()}<label>Aantal kleinste<input type="number" id="cN" value="25" min="1" max="500" style="width:80px"></label></div>
      <div class="btnrow"><button class="btn" id="cAuto">Sluit N kleinste kantoren</button><button class="btn" id="cClear">Wis selectie</button></div><div id="out"></div>`;
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.closed = new Set(); this.update(); };
    $('#cClear').onclick = () => { this.closed = new Set(); this.update(); };
    $('#cAuto').onclick = () => {
      const b = UI.brand, n = +$('#cN').value, l = [];
      for (let j = 0; j < nO; j++) if (hasB(j, b)) l.push([j, brandOfficeDem(REF, j, b)]);
      l.sort((x, y) => x[1] - y[1]); this.closed = new Set(l.slice(0, n).map(x => x[0])); this.update();
    };
    hint('Klik op een kantoor om het te sluiten of te heropenen');
    mapClickHandler = (e, j) => { if (j == null) return false; this.closed.has(j) ? this.closed.delete(j) : this.closed.add(j); this.update(); return true; };
  },
  update() {
    const b = UI.brand, R = REF;
    paintOffices(null, { filterBrand: b });
    highlightOffices(this.closed);
    if (!this.closed.size) {
      paintSectors(R.share[b], { title: `Marktaandeel ${BRANDS[b]}`, fmt: v => pct(v, 0) });
      $('#out').innerHTML = '<p class="sm">Nog geen kantoren gesloten.</p>'; return;
    }
    CUR = compute({ closed: this.closed });
    const v = new Float32Array(nS); for (let i = 0; i < nS; i++) v[i] = CUR.share[b][i] - R.share[b][i];
    paintSectors(v, { kind: 'div', title: `Δ marktaandeel ${BRANDS[b]} (procentpunt)`, fmt: ppf });
    let closedB = 0, closedAll = 0; for (const j of this.closed) { closedB += brandOfficeDem(R, j, b); closedAll += R.officeDem[j]; }
    const loss = R.brandDem[b] - CUR.brandDem[b];
    const bd = BRANDS.map((n, k) => ({ label: n, value: CUR.brandDem[k] - R.brandDem[k] })).sort((x, y) => y.value - x.value);
    const gain = []; for (let j = 0; j < nO; j++) { const d = CUR.officeDem[j] - R.officeDem[j]; if (d > 1) gain.push([j, d]); }
    gain.sort((x, y) => y[1] - x[1]);
    $('#out').innerHTML = tiles([
      { v: f0(this.closed.size), l: 'Gesloten kantoren' },
      { v: f0(closedB), l: `${esc(BRANDS[b])}-potentieel in die kantoren` },
      { v: pct(Math.max(0, 1 - loss / closedB), 0), l: 'Retentie binnen het merk' },
      { v: '−' + f0(loss), l: 'Netto verlies merk (inw.-eq.)', dc: 'neg' },
    ]) + `<h3>Wie wint de vrijgekomen klanten?</h3>${hbar(bd, { fmt: x => sgn(x, f0), diverging: true })}
      <h3>Opvangende kantoren</h3><table><thead><tr><th>Kantoor</th><th class="n">Instroom</th></tr></thead><tbody>${gain.slice(0, 15).map(([j, d]) => officeRow(j, [sgn(d, f0)])).join('')}</tbody></table>
      <h3>Gesloten (${this.closed.size})</h3><table><tbody>${[...this.closed].slice(0, 60).map(j => officeRow(j, [f0(brandOfficeDem(R, j, b))])).join('')}</tbody></table>`;
    bindOfficeRows($('#out'));
  },
  leave() { hint(null); mapClickHandler = null; highlightOffices(new Set()); },
});

reg({
  id: 'banks', group: 'Scenario’s', title: 'Afbouw bankkantoren', desc: 'Kansen voor makelaars en agenten',
  render(el) {
    const groups = {}; for (let j = 0; j < nO; j++) if (OFF.ch[j] === 'bank') { const g = bankGroup(j); groups[g] = (groups[g] || 0) + 1; }
    el.innerHTML = `<h2>Afbouw bankkantoren</h2>
      <p class="lead">Banken sluiten jaar na jaar kantoren. Waar gaan die klanten heen? Het model sluit de bankkantoren met het kleinste verzorgingsgebied en verdeelt hun klanten opnieuw volgens Huff.</p>
      <div class="controls"><label>Bank<select id="bBank"><option value="*">Alle banken (${Object.values(groups).reduce((a, c) => a + c, 0)})</option>${Object.entries(groups).sort((a, b2) => b2[1] - a[1]).map(([g, n]) => `<option value="${esc(g)}">${esc(g)} (${n})</option>`).join('')}</select></label>
        <label>Sluitingspercentage <output id="bO">30%</output><input type="range" id="bPct" min="5" max="100" step="5" value="30"></label></div><div id="out"></div>`;
    $('#bBank').onchange = () => this.update();
    $('#bPct').oninput = e => { $('#bO').textContent = e.target.value + '%'; };
    $('#bPct').onchange = () => this.update();
  },
  update() {
    const g = $('#bBank').value, share = +$('#bPct').value / 100, R = REF;
    const l = []; for (let j = 0; j < nO; j++) if (OFF.ch[j] === 'bank' && (g === '*' || bankGroup(j) === g)) l.push([j, R.officeDem[j]]);
    l.sort((x, y) => x[1] - y[1]);
    const closed = new Set(l.slice(0, Math.round(l.length * share)).map(x => x[0]));
    CUR = compute({ closed });
    let freed = 0; for (const j of closed) freed += R.officeDem[j];
    const byCh = { makelaar: 0, agent: 0, bank: 0, direct: 0 };
    const gain = [];
    for (let j = 0; j < nO; j++) { const d = CUR.officeDem[j] - R.officeDem[j]; if (d > 0 && !closed.has(j)) { byCh[OFF.ch[j]] += d; if (OFF.ch[j] !== 'bank') gain.push([j, d]); } }
    gain.sort((x, y) => y[1] - x[1]);
    const brokerShare = new Float32Array(nS);
    for (let i = 0; i < nS; i++) {
      const base = i * K; let a = 0, c = 0;
      for (let k = 0; k < K; k++) { const j = PAIRS[base + k]; if (j === 65535) break; if (OFF.ch[j] === 'makelaar') { a += CUR.Pm[base + k]; c += R.Pm[base + k]; } }
      brokerShare[i] = a - c;
    }
    paintSectors(brokerShare, { kind: 'div', title: 'Δ aandeel makelaarskanaal (procentpunt)', fmt: ppf });
    paintOffices(null, {});
    highlightOffices(new Set(gain.slice(0, 25).map(x => x[0])));
    const bd = BRANDS.map((n, k) => ({ label: n, value: CUR.brandDem[k] - R.brandDem[k] })).sort((x, y) => y.value - x.value);
    $('#out').innerHTML = tiles([
      { v: f0(closed.size), l: `Gesloten bankkantoren (van ${l.length})` },
      { v: kfmt(freed), l: 'Vrijgekomen klantpotentieel' },
      { v: pct(byCh.makelaar / freed, 0), l: 'Gaat naar makelaars' },
      { v: pct(byCh.agent / freed, 0), l: 'Gaat naar exclusieve agenten' },
    ]) + `<h3>Herverdeling per kanaal</h3>${hbar(CH_LIST.map(c => ({ label: CH_LABEL[c], value: byCh[c] / freed })), { fmt: v => pct(v, 0) })}
      <h3>Effect per merk</h3>${hbar(bd, { fmt: x => sgn(x, kfmt), diverging: true })}
      <h3>Makelaars/agenten met de grootste instroom</h3><p class="sm">Kandidaten voor lokale campagnes richting ex-bankklanten (zwart omrand op de kaart).</p>
      <table><thead><tr><th>Kantoor</th><th class="n">Instroom</th><th class="n">Groei</th></tr></thead><tbody>${gain.slice(0, 25).map(([j, d]) => officeRow(j, [f0(d), sgn(d / R.officeDem[j] * 100, f0) + '%'])).join('')}</tbody></table>`;
    bindOfficeRows($('#out'));
  },
  leave() { highlightOffices(new Set()); },
});
function bankGroup(j) {
  const n = OFF.name[j].toLowerCase();
  if (n.includes('bnp') || n.includes('fortis')) return 'BNP Paribas Fortis';
  if (n.includes('crelan')) return 'Crelan';
  if (n.includes('fintro')) return 'Fintro';
  if (n.includes('belfius')) return 'Belfius';
  if (n.includes('kbc') || n.includes('cbc')) return 'KBC/CBC';
  if (n.includes('ing')) return 'ING';
  for (const b of ['Belfius', 'KBC', 'ING', 'AG', 'AXA']) { const i = BRANDS.indexOf(b); if (i >= 0 && hasB(j, i)) return { AG: 'BNP Paribas Fortis', AXA: 'Crelan' }[b] || b; }
  return 'Overige';
}

reg({
  id: 'mna', group: 'Netwerk', title: 'Overname- en partnerkandidaten', desc: 'Welke makelaars versterken het netwerk het meest?',
  render(el) {
    el.innerHTML = `<h2>Overname- & partnerkandidaten</h2>
      <p class="lead">Voor een netwerk of maatschappij: welke onafhankelijke kantoren die het merk nog <i>niet</i> voeren brengen het meeste incrementele klantpotentieel binnen? <b>Gebiedsfit</b> = aandeel van hun klanten dat in zones zit waar het merk onder zijn nationale aandeel blijft.</p>
      <div class="controls">${brandSelect('ucBrand', 'Netwerk / merk')}
        <label class="inline"><input type="checkbox" id="aAgents"> ook exclusieve agenten</label>
        <label>Sorteer op<select id="aSort"><option value="score">Volume × fit</option><option value="inc">Incrementeel volume</option><option value="fit">Gebiedsfit</option></select></label></div><div id="out"></div>`;
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.update(); };
    $('#aAgents').onchange = () => this.update(); $('#aSort').onchange = () => this.update();
  },
  update() {
    const b = UI.brand, R = REF, nat = R.brandDem[b] / R.totalD, agents = $('#aAgents').checked, sortBy = $('#aSort').value;
    const fit = new Float64Array(nO), ov = new Float64Array(nO);
    for (let i = 0; i < nS; i++) {
      const base = i * K, w = R.share[b][i] < nat ? 1 : 0, S = R.share[b][i];
      for (let k = 0; k < K; k++) { const j = PAIRS[base + k]; if (j === 65535) break; const F = R.D[i] * R.Pm[base + k]; fit[j] += F * w; ov[j] += F * S; }
    }
    const cands = [];
    for (let j = 0; j < nO; j++) {
      if (hasB(j, b)) continue; const ch = OFF.ch[j];
      if (!(ch === 'makelaar' || (agents && ch === 'agent'))) continue;
      const F = R.officeDem[j]; if (F < 1) continue;
      cands.push({ j, inc: F, fit: fit[j] / F, ov: ov[j] / F, score: F * fit[j] / F });
    }
    cands.sort((x, y) => y[sortBy] - x[sortBy]);
    const vals = new Float32Array(nO).fill(NaN), only = new Uint8Array(nO);
    for (const c of cands) { vals[c.j] = c.score; only[c.j] = 1; }
    paintSectors(R.share[b], { title: `Huidig marktaandeel ${BRANDS[b]}`, fmt: v => pct(v, 0) });
    paintOffices(vals, { title: 'Kandidaatscore (volume × fit)', fmt: f0, only });
    highlightOffices(new Set(cands.slice(0, 20).map(c => c.j)));
    const top = cands.slice(0, 40); let s20 = 0; for (const c of cands.slice(0, 20)) s20 += c.inc;
    $('#out').innerHTML = tiles([
      { v: f0(cands.length), l: 'Kandidaten zonder dit merk' },
      { v: kfmt(s20), l: 'Potentieel top-20 samen' },
      { v: sgn(s20 / R.brandDem[b] * 100, f0) + '%', l: `Groei t.o.v. huidig ${esc(BRANDS[b])}-potentieel` },
      { v: pct(nat), l: 'Huidig nationaal aandeel' },
    ]) + `<table><thead><tr><th>Kantoor</th><th class="n">Volume</th><th class="n">Fit</th><th class="n">Overlap</th></tr></thead><tbody>
      ${top.map(c => `<tr data-o="${c.j}"><td><b>${esc(OFF.name[c.j])}</b><div class="sm">${esc(OFF.munty[c.j])} · ${brandTags(c.j) || CH_LABEL[OFF.ch[c.j]]}</div></td><td class="n">${f0(c.inc)}</td><td class="n">${pct(c.fit, 0)}</td><td class="n">${pct(c.ov, 0)}</td></tr>`).join('')}</tbody></table>
      <p class="sm">Overlap = gemiddeld aandeel van het merk in het verzorgingsgebied van de kandidaat. Laag = het kantoor brengt nieuwe markt aan.</p>`;
    bindOfficeRows($('#out'));
  },
  leave() { highlightOffices(new Set()); },
});

reg({
  id: 'competition', group: 'Positie', title: 'Concurrentiedruk & concentratie', desc: 'HHI, kantoordichtheid, marktleider',
  render(el) {
    el.innerHTML = `<h2>Concurrentiedruk</h2>
      <p class="lead">Marktconcentratie op basis van de Huff-aandelen per merk (Herfindahl-Hirschman-index, 0–10.000) en het aantal kantoren dat binnen 10 minuten bereikbaar is.</p>
      <div class="controls"><label>Kaartlaag<select id="cMetric"><option value="hhi">HHI (concentratie)</option><option value="dens">Kantoren binnen 10 min</option><option value="pop">Inwoners per bereikbaar kantoor</option></select></label>${brandSelect('ucBrand', 'Toon leiderschap van')}</div><div id="out"></div>`;
    $('#cMetric').onchange = () => this.update();
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.update(); };
  },
  update() {
    const R = REF, m = $('#cMetric').value, b = UI.brand;
    const hhi = new Float32Array(nS), dens = new Float32Array(nS);
    for (let i = 0; i < nS; i++) {
      let h = 0, tot = 0; for (let k = 0; k < NB; k++) tot += R.share[k][i];
      if (tot > 0) for (let k = 0; k < NB; k++) { const s = R.share[k][i] / tot; h += s * s; }
      hhi[i] = h * 10000;
      const base = i * K; let n = 0; for (let k = 0; k < K; k++) { if (PAIRS[base + k] === 65535) break; if (TT.base[base + k] <= 40) n++; } dens[i] = n;
    }
    if (m === 'hhi') paintSectors(hhi, { title: 'HHI (hoger = geconcentreerder)', fmt: f0 });
    else if (m === 'dens') paintSectors(dens, { title: 'Kantoren binnen 10 min (≥60 = 60+)', fmt: f0, breaks: [3, 6, 10, 15, 25, 40] });
    else { const v = new Float32Array(nS); for (let i = 0; i < nS; i++) v[i] = dens[i] ? SEC.pop[i] / dens[i] : NaN; paintSectors(v, { title: 'Inwoners sector per bereikbaar kantoor', fmt: f0 }); }
    paintOffices(null, {});
    const mun = munAgg(i => { const o = { d: R.D[i], h: R.D[i] * hhi[i], pop: SEC.pop[i] }; for (let k = 0; k < NB; k++) o['s' + k] = R.D[i] * R.share[k][i]; return o; });
    mun.forEach(x => { let best = 0; for (let k = 1; k < NB; k++) if (x['s' + k] > x['s' + best]) best = k; x.lead = best; x.hhi = x.h / x.d; });
    const leads = BRANDS.map((n, k) => ({ label: n, value: mun.filter(x => x.lead === k).length, hl: k === b })).sort((x, y) => y.value - x.value);
    const big = mun.filter(x => x.pop > 10000).sort((x, y) => y.hhi - x.hhi);
    $('#out').innerHTML = `<h3>Aantal gemeenten waar het merk marktleider is</h3>${hbar(leads, { fmt: f0 })}
      <h3>Meest geconcentreerde gemeenten (>10.000 inw.)</h3><table><thead><tr><th>Gemeente</th><th class="n">HHI</th><th>Leider</th><th class="n">${esc(BRANDS[b])}</th></tr></thead><tbody>
      ${big.slice(0, 15).map(x => `<tr data-m="${x.refnis}"><td><b>${esc(x.name)}</b></td><td class="n">${f0(x.hhi)}</td><td>${esc(BRANDS[x.lead])} ${pct(x['s' + x.lead] / x.d, 0)}</td><td class="n">${pct(x['s' + b] / x.d, 0)}</td></tr>`).join('')}</tbody></table>
      <h3>Meest versnipperde markten</h3><table><thead><tr><th>Gemeente</th><th class="n">HHI</th><th>Leider</th><th class="n">${esc(BRANDS[b])}</th></tr></thead><tbody>
      ${big.slice(-10).reverse().map(x => `<tr data-m="${x.refnis}"><td><b>${esc(x.name)}</b></td><td class="n">${f0(x.hhi)}</td><td>${esc(BRANDS[x.lead])} ${pct(x['s' + x.lead] / x.d, 0)}</td><td class="n">${pct(x['s' + b] / x.d, 0)}</td></tr>`).join('')}</tbody></table>`;
    bindMunRows($('#out'));
  },
});

reg({
  id: 'potential', group: 'Positie', title: 'Potentieel per productlijn', desc: 'Demografie & koopkracht (Statbel)',
  render(el) {
    el.innerHTML = `<h2>Potentieel per productlijn</h2>
      <p class="lead">Klantpotentieel uit Statbel-bevolking per sector, gewogen naar leeftijdsprofiel en fiscaal inkomen van de gemeente. Wijzig de productlijn om te zien waar bv. vermogensplanning of 65+-producten het meeste potentieel hebben, en hoeveel potentieel er per kantoor van het merk is.</p>
      <div class="controls"><label>Productlijn<select id="kProd">${$('#pProduct').innerHTML}</select></label>${brandSelect()}</div><div id="out"></div>`;
    $('#kProd').value = P.product;
    $('#kProd').onchange = e => { P.product = e.target.value; $('#pProduct').value = P.product; paramsChanged(); };
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.update(); };
  },
  update() {
    const R = REF, b = UI.brand;
    paintSectors(R.D, { title: 'Klantpotentieel per sector (inw.-eq.)', fmt: f0 });
    paintOffices(null, { filterBrand: b });
    const oc = {}; for (let j = 0; j < nO; j++) if (hasB(j, b)) { const r = SEC.refnis[OFF.sector[j]]; oc[r] = (oc[r] || 0) + 1 / offNb[j]; }
    const mun = munAgg(i => ({ d: R.D[i], s: R.D[i] * R.share[b][i], pop: SEC.pop[i] }));
    mun.forEach(x => { x.per = x.d / Math.max(0.5, oc[x.refnis] || 0); });
    const under = mun.filter(x => x.pop > 8000).sort((x, y) => y.per - x.per);
    const prov = {}; for (let i = 0; i < nS; i++) prov[SEC.prov[i]] = (prov[SEC.prov[i]] || 0) + R.D[i];
    const pb = Object.entries(prov).map(([p, v]) => ({ label: p.replace('Brussels Hoofdstedelijk Gewest', 'Brussel').replace('-Vlaanderen', '-Vl.'), value: v / R.totalD })).sort((x, y) => y.value - x.value);
    $('#out').innerHTML = `<h3>Verdeling potentieel per provincie</h3>${hbar(pb, { fmt: v => pct(v) })}
      <h3>Meeste potentieel per ${esc(BRANDS[b])}-kantoor (gemeenten >8.000 inw.)</h3><p class="sm">Kantoren met meerdere merken tellen fractioneel mee.</p>
      <table><thead><tr><th>Gemeente</th><th class="n">Potentieel</th><th class="n">Kant.</th><th class="n">Per kant.</th><th class="n">Aandeel</th></tr></thead><tbody>
      ${under.slice(0, 25).map(x => `<tr data-m="${x.refnis}"><td><b>${esc(x.name)}</b><div class="sm">${esc(x.prov)}</div></td><td class="n">${f0(x.d)}</td><td class="n">${f1(oc[x.refnis] || 0)}</td><td class="n">${f0(x.per)}</td><td class="n">${pct(x.s / x.d, 0)}</td></tr>`).join('')}</tbody></table>`;
    bindMunRows($('#out'));
  },
});

reg({
  id: 'pt', group: 'Netwerk', title: 'OV-bereikbaarheid kantoren', desc: 'GTFS: NMBS, De Lijn, MIVB, TEC',
  render(el) {
    el.innerHTML = `<h2>OV-bereikbaarheid</h2>
      <p class="lead">OV-score = aantal vertrekken op een werkdag van haltes binnen 800 m, gewogen naar wandelafstand (GTFS van NMBS, De Lijn, MIVB en TEC). Relevant voor klanten zonder auto, jongeren en stedelijke kantoren. Gebruik de modelparameter <i>Gewicht OV-bereikbaarheid</i> om het effect op de marktaandelen te zien.</p>
      <div class="controls">${brandSelect()}<label>Drempel "goed bereikbaar"<select id="pThr"><option value="100">≥ 100</option><option value="300" selected>≥ 300</option><option value="1000">≥ 1.000</option></select></label></div><div id="out"></div>`;
    $('#ucBrand').onchange = e => { UI.brand = +e.target.value; this.update(); };
    $('#pThr').onchange = () => this.update();
  },
  update() {
    const b = UI.brand, thr = +$('#pThr').value;
    paintSectors(Float32Array.from(SEC.pt), { title: 'OV-score woonsector (vertrekken/dag)', fmt: f0, breaks: [10, 50, 150, 300, 700, 1500] });
    const v = Float32Array.from(OFF.pt);
    const only = new Uint8Array(nO); for (let j = 0; j < nO; j++) only[j] = hasB(j, b);
    paintOffices(v, { title: 'OV-score kantoor', fmt: f0, only });
    const rows = BRANDS.map((n, k) => { let c = 0, g = 0; const st = []; for (let j = 0; j < nO; j++) if (hasB(j, k)) { c++; if (OFF.pt[j] >= thr) g++; st.push(OFF.station[j]); } st.sort((x, y) => x - y); return { label: n, value: c ? g / c : 0, c, med: st[Math.floor(st.length / 2)] || 0, hl: k === b }; }).sort((x, y) => y.value - x.value);
    let lowPop = 0, pop = 0; for (let i = 0; i < nS; i++) { pop += SEC.pop[i]; if (SEC.pt[i] < 50) lowPop += SEC.pop[i]; }
    const sel = rows.find(r => r.label === BRANDS[b]);
    $('#out').innerHTML = tiles([
      { v: pct(sel.value, 0), l: `${esc(BRANDS[b])}-kantoren goed OV-bereikbaar` },
      { v: f1(sel.med / 1000) + ' km', l: 'Mediane afstand tot treinstation' },
      { v: pct(lowPop / pop, 0), l: 'Inwoners met zwak OV (< 50 vertrekken)' },
      { v: f0(sel.c), l: 'Kantoren van het merk' },
    ]) + `<h3>Aandeel kantoren goed OV-bereikbaar, per merk</h3>${hbar(rows, { fmt: v => pct(v, 0) })}`;
  },
});

reg({
  id: 'about', group: 'Info', title: 'Methode & bronnen', desc: 'Hoe het model rekent',
  render(el) {
    el.innerHTML = `<div class="method"><h2>Methode & bronnen</h2>
      <h3>Huff-gravitatiemodel</h3>
      <p>Voor elke statistische sector <i>i</i> en kantoor <i>j</i>: <code>P(i→j) = A<sub>j</sub>·t<sub>ij</sub><sup>−λ</sup> / Σ<sub>k</sub> A<sub>k</sub>·t<sub>ik</sub><sup>−λ</sup></code>.
      Per sector worden de 60 snelst bereikbare kantoren (≤ 35 min) meegenomen. Kantoren met meerdere maatschappijen verdelen hun kans gelijk over die merken.</p>
      <ul>
        <li><b>t<sub>ij</sub></b>: rijtijd auto in minuten, berekend met Dijkstra op het OSM-wegennet (snelheid volgens wegklasse en maxspeed), plus aansluittijd tot het netwerk.</li>
        <li><b>A<sub>j</sub></b>: kanaalgewicht × (1 + bonus × extra maatschappijen) × (1 + OV-gewicht × OV-index).</li>
        <li><b>Vraag</b>: bevolking per sector (Statbel 2025) × leeftijdsprofiel van de gemeente (2026) × inkomensindex<sup>ε</sup> (fiscale inkomens 2023).</li>
        <li><b>Nieuwe locaties</b>: rijtijden benaderd met een per sector gekalibreerde min/km-factor uit het wegennet.</li>
        <li><b>Scenario's</b>: het wegennet wordt opnieuw gewogen of onderbroken en alle reistijden worden herberekend. Zone-ingrepen (LEZ, werven) tellen extra minuten op bij kantoren in de zone; de LEZ-zones zijn cirkelvormige benaderingen.</li>
      </ul>
      <div class="note">Het model schat <b>relatief</b> klantpotentieel (inwoner-equivalenten), geen polissen of premies. Er is geen kantoorgrootte of omzet beschikbaar; kalibratie op echte portefeuilledata (bv. postcode-aandelen) maakt λ en de kanaalgewichten betrouwbaarder. Allianz ontbreekt in de kantorenlijst. Bankkantoren uit OSM zijn gekoppeld aan hun bankverzekeraar.</div>
      <h3>Bronnen</h3><ul>${META.sources.map(s => `<li><a href="${esc(s.url)}" target="_blank" rel="noopener">${esc(s.name)}</a></li>`).join('')}<li>Kantorenlijst: eigen dataset (locators van maatschappijen, FSMA, OSM), ${f0(nO)} kantoren in België</li></ul>
      <h3>Kaart</h3><p>Ondergrond © OpenStreetMap-bijdragers, © CARTO. Visualisatie: MapLibre GL.</p></div>`;
  },
  update() { clearSectors(); paintOffices(null, {}); },
});

// ---------- navigatie & parameters ----------
function buildNav() {
  let h = '', g = null, n = 0;
  const order = ['Positie', 'Netwerk', 'Scenario’s', 'Info'];
  UC.sort((a, b) => order.indexOf(a.group) - order.indexOf(b.group));
  for (const u of UC) {
    if (u.group !== g) { g = u.group; h += `<div class="group">${esc(g)}</div>`; }
    h += `<button data-uc="${u.id}"><span class="num">${++n}</span><span><span class="t">${esc(u.title)}</span><span class="d">${esc(u.desc)}</span></span></button>`;
  }
  $('#usecases').innerHTML = h;
  $('#usecases').querySelectorAll('button').forEach(b => b.onclick = () => activate(b.dataset.uc));
}
function activate(id) {
  if (ucActive?.leave) ucActive.leave();
  mapClickHandler = null; hint(null); setMarks([]); highlightOffices(new Set());
  if (popup) { popup.remove(); popup = null; }
  ucActive = UC.find(u => u.id === id);
  $('#usecases').querySelectorAll('button').forEach(b => b.setAttribute('aria-current', b.dataset.uc === id));
  const el = $('#panel'); el.scrollTop = 0;
  ucActive.render(el);
  ucActive.update();
  try { localStorage.setItem('huff_uc', id); } catch (e) { /* opslag niet beschikbaar */ }
}
let pTimer = null;
function paramsChanged() {
  clearTimeout(pTimer);
  pTimer = setTimeout(() => { recomputeRef(); renderGlobalKpis(); ucActive?.update(); }, 120);
}
function bindParams() {
  $('#toggleParams').onclick = e => { const p = $('#params'); p.hidden = !p.hidden; e.target.setAttribute('aria-expanded', !p.hidden); setTimeout(() => map.resize(), 0); };
  const bindR = (id, out, key, d = 1) => $('#' + id).addEventListener('input', e => { P[key] = +e.target.value; $('#' + out).textContent = (+e.target.value).toFixed(d); paramsChanged(); });
  bindR('pLambda', 'oLambda', 'lambda'); bindR('pInc', 'oInc', 'inc'); bindR('pMulti', 'oMulti', 'multi', 2); bindR('pPt', 'oPt', 'pt', 2);
  $('#pProduct').onchange = e => { P.product = e.target.value; const k = $('#kProd'); if (k) k.value = P.product; paramsChanged(); };
  [['wMakelaar', 'makelaar'], ['wAgent', 'agent'], ['wBank', 'bank'], ['wDirect', 'direct']].forEach(([id, k]) => $('#' + id).addEventListener('change', e => { P.w[k] = Math.max(0, +e.target.value); paramsChanged(); }));
}
function renderGlobalKpis() {
  $('#globalKpis').innerHTML = [[f0(nO), 'kantoren'], [f0(nS), 'sectoren'], [f1(META.population / 1e6) + ' mln', 'inwoners'], [kfmt(REF.totalD), 'potentieel']].map(([v, l]) => `<div class="kpi"><b>${v}</b><span>${l}</span></div>`).join('');
}

(async function main() {
  try {
    await loadAll();
    setLoading('Kaart opbouwen…');
    await initMap();
    setLoading('Huff-model doorrekenen…');
    await new Promise(r => setTimeout(r, 0));
    recomputeRef();
    renderGlobalKpis(); buildNav(); bindParams();
    let start = 'share'; try { start = localStorage.getItem('huff_uc') || 'share'; } catch (e) { /* geen opslag */ }
    activate(UC.some(u => u.id === start) ? start : 'share');
    setLoading(null);
  } catch (err) {
    setLoading('Laden mislukt: ' + err.message + ' — start de pagina via een lokale webserver (zie README).');
    throw err;
  }
})();
