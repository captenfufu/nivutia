/* =======================================================================
   הניווטיה — משחק הניווט: מהמפה אל השטח
   תבליט אמיתי (רשת גובה 25 מ׳ ברשת ישראל החדשה) · מפה טופוגרפית שנבנית
   בדפדפן · מבט בשטח (raycasting) · הליכה בצעדים · ציר אידיאלי (A*)
   ======================================================================= */
'use strict';

/* ---------- 0. קבועים ועזרים ---------- */
const TAU = Math.PI * 2;
const deg = r => r * 180 / Math.PI;
const rad = d => d * Math.PI / 180;
const norm360 = a => ((a % 360) + 360) % 360;
const angDiff = (a, b) => ((a - b + 540) % 360) - 180;   // הפרש זוויות בטווח ‎-180..180
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const azimuth = (dx, dy) => norm360(deg(Math.atan2(dx, dy)));   // dx=מזרח, dy=צפון
const fmtDist = m => m >= 1000 ? (m / 1000).toFixed(2) + ' ק״מ' : Math.round(m) + ' מ׳';
const fmtTime = s => { const m = Math.round(s / 60); return Math.floor(m / 60) + ':' + String(m % 60).padStart(2, '0'); };
const fmtNZ = (E, N) => `${Math.round(E / 10) * 10} / ${Math.round(N / 10) * 10}`;
const $ = id => document.getElementById(id);

const DECL = 4.9;      // סטייה מגנטית בישראל, מזרחה (כמו בשאר האתר): מגנטי = רשת − 4.9°
const PACE = 1.5;      // מ׳ לצמד צעדים בשטח מישורי (כ־67 צמדים ל־100 מ׳)
const EYE = 1.7;       // גובה העין מעל הקרקע
const MAXG = 1.0;      // שיפוע מרבי עביר (45°) — מעבר לזה: מצוק
const FOV = 70;        // שדה הראייה במבט בשטח (מעלות)
const MPX = 0.2;       // פיקסלים למטר בבסיס המפה (5 מ׳ לפיקסל)

const LEVELS = {
  easy: { name: 'טירון', targetShown: true, cursorNZ: true, ruler: 'full', meters: true, drift: false, distRange: [1100, 1900] },
  mid:  { name: 'לוחם', targetShown: false, cursorNZ: false, ruler: 'grid', meters: false, drift: false, distRange: [1500, 2500] },
  hard: { name: 'מנווט מוביל', targetShown: false, cursorNZ: false, ruler: 'grid', meters: false, drift: true, distRange: [1900, 3100] },
};

// מהירות הליכה לפי שיפוע (Tobler), במ׳ לשנייה
const tobler = g => 6 * Math.exp(-3.5 * Math.abs(g + 0.05)) / 3.6;
// אורך צמד צעדים (אופקי) לפי שיפוע — בעלייה ובירידה הצעד מתקצר
const strideFor = g => PACE * Math.max(0.5, Math.cos(Math.atan(g)) * (1 - (g > 0 ? 0.6 : 0.5) * Math.abs(g)));

/* ---------- רעש ערכי (לצמחייה ולמרקם הקרקע) ---------- */
function hash2(x, y) {
  let h = (Math.imul(x, 374761393) + Math.imul(y, 668265263)) | 0;
  h = Math.imul(h ^ (h >>> 13), 1274126177);
  return ((h ^ (h >>> 16)) >>> 0) / 4294967296;
}
function vnoise(x, y) {
  const xi = Math.floor(x), yi = Math.floor(y), fx = x - xi, fy = y - yi;
  const u = fx * fx * (3 - 2 * fx), v = fy * fy * (3 - 2 * fy);
  const a = hash2(xi, yi), b = hash2(xi + 1, yi), c = hash2(xi, yi + 1), d = hash2(xi + 1, yi + 1);
  return a + (b - a) * u + (c - a) * v + (a - b - c + d) * u * v;
}
// מדד צמחייה 0..1 — משותף למפה ולמבט בשטח, כך שכתם ירוק במפה = חורש בשטח
const vegIndex = (E, N) => vnoise(E / 170, N / 170) * 0.7 + vnoise(E / 55 + 31.7, N / 55 - 12.3) * 0.3;
const VEG_TH = { north: 0.56, center: 0.66, desert: 2 };

/* =======================================================================
   1. נתוני השטח
   ======================================================================= */
let REGIONS = [];
let T = null;          // השטח הפעיל: {meta, h, shade, slope, veg, nx, ny, e0, n0, cell, nTop}

async function loadRegions() {
  const r = await fetch('assets/game/regions.json');
  REGIONS = await r.json();
}

async function loadTerrain(meta) {
  const buf = await (await fetch(`assets/game/${meta.id}.bin`)).arrayBuffer();
  const raw = new Int16Array(buf);
  const { nx, ny, cell, e0, n0 } = meta;
  const h = new Float32Array(nx * ny);
  for (let k = 0; k < h.length; k++) h[k] = raw[k] / 10;
  // הצללה (שמש מצפון־מערב, 45°) ושיפוע לכל תא
  const shade = new Float32Array(nx * ny), slope = new Float32Array(nx * ny), veg = new Uint8Array(nx * ny);
  const sAz = rad(315), sEl = rad(45);
  const L = [Math.sin(sAz) * Math.cos(sEl), Math.cos(sAz) * Math.cos(sEl), Math.sin(sEl)];
  const th = VEG_TH[meta.biome];
  for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
    const k = j * nx + i;
    const dzx = (h[j * nx + Math.min(nx - 1, i + 1)] - h[j * nx + Math.max(0, i - 1)]) / (2 * cell);
    const dzy = (h[Math.min(ny - 1, j + 1) * nx + i] - h[Math.max(0, j - 1) * nx + i]) / (2 * cell);
    const len = Math.hypot(dzx, dzy, 1);
    shade[k] = Math.max(0, (-dzx * L[0] - dzy * L[1] + L[2]) / len);
    slope[k] = Math.atan(Math.hypot(dzx, dzy));
    veg[k] = (vegIndex(e0 + i * cell, n0 + j * cell) > th && slope[k] < 0.6) ? 1 : 0;
  }
  // מסכת ערוצים (לצביעת אפיקים במבט בשטח)
  const wet = new Float32Array(nx * ny);
  for (const ln of meta.streams) {
    const w = clamp(0.35 + 0.25 * Math.log10(ln[0] / 120), 0.35, 1);
    for (let q = 1; q + 1 < ln.length; q += 2) { const k = ln[q + 1] * nx + ln[q]; if (w > wet[k]) wet[k] = w; }
  }
  T = { meta, h, shade, slope, veg, wet, nx, ny, cell, e0, n0, nTop: n0 + (ny - 1) * cell, size: (nx - 1) * cell };
}

// גובה (אינטרפולציה בילינארית) בנקודת ITM
function hAt(E, N) {
  const x = clamp((E - T.e0) / T.cell, 0, T.nx - 1.0001), y = clamp((N - T.n0) / T.cell, 0, T.ny - 1.0001);
  const i = x | 0, j = y | 0, fx = x - i, fy = y - j, k = j * T.nx + i, H = T.h;
  const a = H[k], b = H[k + 1], c = H[k + T.nx], d = H[k + T.nx + 1];
  return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
}
const inside = (E, N, m = 0) => E >= T.e0 + m && E <= T.e0 + T.size - m && N >= T.n0 + m && N <= T.nTop - m;
// שיפוע (עלייה/מרחק) בכיוון האזימוט
const gradeAlong = (E, N, az, span = 12.5) => {
  const s = Math.sin(rad(az)), c = Math.cos(rad(az));
  return (hAt(E + s * span, N + c * span) - hAt(E - s * span, N - c * span)) / (2 * span);
};

/* =======================================================================
   2. ציר אידיאלי — A* על רשת הגובה, עלות = זמן הליכה (Tobler)
   ======================================================================= */
function idealRoute(A, B) {
  const { nx, ny, cell, h } = T;
  const toIdx = p => Math.round((p.N - T.n0) / cell) * nx + Math.round((p.E - T.e0) / cell);
  const s = toIdx(A), g = toIdx(B), gi = g % nx, gj = (g / nx) | 0;
  const cost = new Float64Array(nx * ny).fill(Infinity), from = new Int32Array(nx * ny).fill(-1);
  const closed = new Uint8Array(nx * ny);
  const vmax = 6 / 3.6;
  const heur = k => Math.hypot((k % nx) - gi, ((k / nx) | 0) - gj) * cell / vmax;
  // ערימה בינארית פשוטה
  const hk = [], hf = [];
  const push = (k, f) => {
    let n = hk.length; hk.push(k); hf.push(f);
    while (n > 0) { const p = (n - 1) >> 1; if (hf[p] <= hf[n]) break; [hk[p], hk[n]] = [hk[n], hk[p]]; [hf[p], hf[n]] = [hf[n], hf[p]]; n = p; }
  };
  const pop = () => {
    const top = hk[0], lk = hk.pop(), lf = hf.pop();
    if (hk.length) {
      hk[0] = lk; hf[0] = lf; let n = 0;
      for (;;) {
        const l = 2 * n + 1, r = l + 1; let m = n;
        if (l < hk.length && hf[l] < hf[m]) m = l;
        if (r < hk.length && hf[r] < hf[m]) m = r;
        if (m === n) break;
        [hk[m], hk[n]] = [hk[n], hk[m]]; [hf[m], hf[n]] = [hf[n], hf[m]]; n = m;
      }
    }
    return top;
  };
  const NB = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [1, -1], [-1, 1], [-1, -1]];
  cost[s] = 0; push(s, heur(s));
  while (hk.length) {
    const c = pop();
    if (closed[c]) continue;
    closed[c] = 1;
    if (c === g) break;
    const ci = c % nx, cj = (c / nx) | 0;
    for (const [di, dj] of NB) {
      const ii = ci + di, jj = cj + dj;
      if (ii < 0 || jj < 0 || ii >= nx || jj >= ny) continue;
      const n = jj * nx + ii;
      if (closed[n]) continue;
      const d = cell * (di && dj ? Math.SQRT2 : 1), gr = (h[n] - h[c]) / d;
      if (Math.abs(gr) > MAXG) continue;
      const nc = cost[c] + d * Math.sqrt(1 + gr * gr) / tobler(gr);
      if (nc < cost[n]) { cost[n] = nc; from[n] = c; push(n, nc + heur(n)); }
    }
  }
  if (!isFinite(cost[g])) return null;
  const pts = [];
  for (let k = g; k !== -1; k = from[k]) pts.push({ E: T.e0 + (k % nx) * cell, N: T.n0 + ((k / nx) | 0) * cell });
  pts.reverse();
  pts[0] = { E: A.E, N: A.N }; pts[pts.length - 1] = { E: B.E, N: B.N };
  return pts;
}

// הערכת מסלול: אורך, זמן, טיפוס מצטבר, והאם יש קטע בלתי עביר
function evalPath(pts) {
  let dist = 0, time = 0, climb = 0, blocked = false;
  for (let k = 1; k < pts.length; k++) {
    const a = pts[k - 1], b = pts[k], L = Math.hypot(b.E - a.E, b.N - a.N);
    const n = Math.max(1, Math.ceil(L / 10));
    let hp = hAt(a.E, a.N);
    for (let s = 1; s <= n; s++) {
      const E = a.E + (b.E - a.E) * s / n, N = a.N + (b.N - a.N) * s / n, hh = hAt(E, N), d = L / n, gr = (hh - hp) / (d || 1);
      if (Math.abs(gr) > MAXG * 1.05) blocked = true;
      dist += d; time += d * Math.sqrt(1 + gr * gr) / tobler(gr); if (hh > hp) climb += hh - hp; hp = hh;
    }
  }
  return { dist, time, climb, blocked };
}

/* =======================================================================
   3. בסיס המפה הטופוגרפית (נבנה פעם אחת לכל גזרה)
   ======================================================================= */
let mapBase = null;
const MAPOPT = { strong: false };   // הצללת תבליט מודגשת
const bx = E => (E - T.e0) * MPX, by = N => (T.nTop - N) * MPX;

function buildMapBase() {
  const { nx, ny, cell, h, shade, veg, meta } = T;
  const W = Math.round(T.size * MPX) + 1;
  const cv = document.createElement('canvas'); cv.width = cv.height = W;
  const ctx = cv.getContext('2d');

  // 3.1 רקע: נייר + צמחייה + הצללת תבליט עדינה
  const small = document.createElement('canvas'); small.width = nx; small.height = ny;
  const sctx = small.getContext('2d'), img = sctx.createImageData(nx, ny);
  const paper = meta.biome === 'desert' ? [247, 238, 218] : [249, 246, 234];
  for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
    const k = j * nx + i, p = ((ny - 1 - j) * nx + i) * 4;
    let c = veg[k] ? [207, 227, 180] : paper;
    const m = MAPOPT.strong ? 0.48 + 0.7 * shade[k] : 0.8 + 0.26 * shade[k];
    img.data[p] = clamp(c[0] * m, 0, 255); img.data[p + 1] = clamp(c[1] * m, 0, 255); img.data[p + 2] = clamp(c[2] * m, 0, 255); img.data[p + 3] = 255;
  }
  sctx.putImageData(img, 0, 0);
  ctx.imageSmoothingEnabled = true;
  ctx.drawImage(small, -cell * MPX / 2, -cell * MPX / 2, nx * cell * MPX, ny * cell * MPX);

  const px = (i) => i * cell * MPX, py = (j) => (ny - 1 - j) * cell * MPX;

  // 3.2 ערוצים
  ctx.strokeStyle = '#3b7fb3'; ctx.lineJoin = ctx.lineCap = 'round';
  if (meta.biome === 'desert') ctx.setLineDash([7, 4]);
  for (const ln of meta.streams) {
    const acc = ln[0], w = clamp(0.7 + 0.75 * Math.log10(acc / 120), 0.7, 3);
    ctx.lineWidth = w; ctx.beginPath();
    // החלקה: עוברים דרך נקודות האמצע (Chaikin פשוט)
    let x0 = px(ln[1]), y0 = py(ln[2]);
    ctx.moveTo(x0, y0);
    for (let q = 3; q + 1 < ln.length; q += 2) {
      const x1 = px(ln[q]), y1 = py(ln[q + 1]);
      ctx.quadraticCurveTo(x0, y0, (x0 + x1) / 2, (y0 + y1) / 2);
      x0 = x1; y0 = y1;
    }
    ctx.lineTo(x0, y0); ctx.stroke();
  }
  ctx.setLineDash([]);

  // 3.3 קווי גובה — marching squares
  const INT = 10, IDX = 50;
  const thin = new Path2D(), thick = new Path2D(), labels = [];
  for (let j = 0; j < ny - 1; j++) for (let i = 0; i < nx - 1; i++) {
    const a = h[j * nx + i], b = h[j * nx + i + 1], c = h[(j + 1) * nx + i + 1], d = h[(j + 1) * nx + i];
    const lo = Math.min(a, b, c, d), hi = Math.max(a, b, c, d);
    for (let L = Math.ceil(lo / INT) * INT; L <= hi; L += INT) {
      if (L === lo && L === hi) continue;
      const P = [];
      const edge = (v1, v2, x1, y1, x2, y2) => {
        if ((v1 < L) !== (v2 < L)) { const t = (L - v1) / (v2 - v1); P.push([x1 + (x2 - x1) * t, y1 + (y2 - y1) * t]); }
      };
      edge(a, b, i, j, i + 1, j); edge(b, c, i + 1, j, i + 1, j + 1);
      edge(c, d, i + 1, j + 1, i, j + 1); edge(d, a, i, j + 1, i, j);
      if (P.length < 2) continue;
      const path = L % IDX === 0 ? thick : thin;
      for (let q = 0; q + 1 < P.length; q += 2) {
        const x1 = px(P[q][0]), y1 = py(P[q][1]), x2 = px(P[q + 1][0]), y2 = py(P[q + 1][1]);
        path.moveTo(x1, y1); path.lineTo(x2, y2);
        if (path === thick && T.slope[j * nx + i] < 0.5) labels.push([(x1 + x2) / 2, (y1 + y2) / 2, Math.atan2(y2 - y1, x2 - x1), L]);
      }
    }
  }
  ctx.strokeStyle = 'rgba(169,116,58,0.85)'; ctx.lineWidth = 0.75; ctx.stroke(thin);
  ctx.strokeStyle = 'rgba(150,96,40,0.95)'; ctx.lineWidth = 1.6; ctx.stroke(thick);

  // תוויות גובה על קווים מודגשים — בפיזור, בלי צפיפות
  const placed = [];
  ctx.font = '600 11px Heebo, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  for (let q = labels.length - 1; q > 0; q--) { const r = Math.floor(hash2(q, 7) * (q + 1)); [labels[q], labels[r]] = [labels[r], labels[q]]; }
  for (const [x, y, a0, L] of labels) {
    if (placed.length > 140) break;
    if (placed.some(p => Math.hypot(p[0] - x, p[1] - y) < 150)) continue;
    placed.push([x, y]);
    let a = a0; if (a > Math.PI / 2) a -= Math.PI; if (a < -Math.PI / 2) a += Math.PI;
    ctx.save(); ctx.translate(x, y); ctx.rotate(a);
    const txt = String(L), w = ctx.measureText(txt).width + 4;
    ctx.fillStyle = 'rgba(249,246,234,0.95)'; ctx.fillRect(-w / 2, -6, w, 12);
    ctx.fillStyle = '#8a5a26'; ctx.fillText(txt, 0, 0.5); ctx.restore();
  }

  // 3.4 רשת ישראל החדשה (כחול) כל 1 ק״מ + תוויות ק״מ
  ctx.strokeStyle = 'rgba(42,100,200,0.75)'; ctx.lineWidth = 1;
  ctx.font = '700 12px Heebo, sans-serif'; ctx.fillStyle = '#1f4fa0';
  for (let E = Math.ceil(T.e0 / 1000) * 1000; E <= T.e0 + T.size; E += 1000) {
    const x = bx(E); ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x, W); ctx.stroke();
  }
  for (let N = Math.ceil(T.n0 / 1000) * 1000; N <= T.nTop; N += 1000) {
    const y = by(N); ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke();
  }
  for (let E = Math.ceil(T.e0 / 1000) * 1000; E <= T.e0 + T.size; E += 1000)
    for (let N = Math.ceil(T.n0 / 1000) * 1000 + 500; N <= T.nTop; N += 2000) {
      const t = String(E / 1000); ctx.save(); ctx.translate(bx(E) + 2, by(N)); ctx.rotate(-Math.PI / 2);
      ctx.textAlign = 'center'; ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(255,255,255,0.85)'; ctx.strokeText(t, 0, -4);
      ctx.fillText(t, 0, -4); ctx.restore();
    }
  ctx.strokeStyle = 'rgba(42,100,200,0.75)';
  for (let N = Math.ceil(T.n0 / 1000) * 1000; N <= T.nTop; N += 1000)
    for (let E = Math.ceil(T.e0 / 1000) * 1000 + 500; E <= T.e0 + T.size; E += 2000) {
      const t = String(N / 1000); ctx.textAlign = 'center';
      ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(255,255,255,0.85)'; ctx.strokeText(t, bx(E), by(N) - 7);
      ctx.fillText(t, bx(E), by(N) - 7);
    }

  // 3.5 נקודות גובה
  ctx.font = '700 11px Heebo, sans-serif'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
  for (const [i, j, z] of meta.peaks) {
    const x = px(i), y = py(j);
    ctx.fillStyle = '#111'; ctx.beginPath(); ctx.moveTo(x, y - 4); ctx.lineTo(x + 4, y + 3); ctx.lineTo(x - 4, y + 3); ctx.closePath(); ctx.fill();
    ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(255,255,255,0.9)'; ctx.strokeText(String(z), x + 6, y); ctx.fillText(String(z), x + 6, y);
  }
  ctx.strokeStyle = '#333'; ctx.lineWidth = 2; ctx.strokeRect(1, 1, W - 2, W - 2);
  mapBase = cv;
}

/* =======================================================================
   4. מצב המשחק
   ======================================================================= */
const G = {
  level: 'mid', lv: LEVELS.mid, region: null,
  start: null, target: null, targetDesc: '', pos: null, hd: 0, drift: 0,
  paces: 0, legPaces: 0, walked: 0, time: 0, path: [], ideal: null,
  targetKnown: false, dotTries: 0, dotErr: null,
  marks: [], ruler: [], gps: 0, gpsUntil: 0, guess: null,
  bearings: [], backLines: [], pendingBearing: null,
  phase: 'idle',  // idle | dot | nav | final | done
  done: {}, tool: 'pan', oriented: false, everOriented: false,
};

/* ---------- בחירת נקודות מוצא ויעד על תוואים ---------- */
function candidates() {
  const { meta, cell, nx } = T, out = [];
  const W = (i, j) => ({ E: T.e0 + i * cell, N: T.n0 + j * cell });
  for (const [i, j, z] of meta.peaks) out.push({ ...W(i, j), type: 'peak', desc: `ראש גבעה — נקודת גובה ${z}` });
  for (const ln of meta.streams) {
    const n = (ln.length - 1) / 2, ei = ln[ln.length - 2], ej = ln[ln.length - 1];
    if (n > 8 && ei > 2 && ej > 2 && ei < nx - 3 && ej < T.ny - 3) out.push({ ...W(ei, ej), type: 'junction', desc: 'מפגש ערוצים' });
    if (n > 30) { const q = 1 + 2 * Math.floor(n / 2); out.push({ ...W(ln[q], ln[q + 1]), type: 'stream', desc: 'בערוץ (אפיק נחל)' }); }
  }
  return out.filter(p => inside(p.E, p.N, 1100) && T.slope[Math.round((p.N - T.n0) / cell) * nx + Math.round((p.E - T.e0) / cell)] < 0.55);
}

function pickMission() {
  const C = candidates(), [dmin, dmax] = G.lv.distRange;
  const starts = C.filter(c => c.type === 'peak');
  const rnd = a => a[Math.floor(Math.random() * a.length)];
  for (let tries = 0; tries < 400; tries++) {
    const s = rnd(starts.length > 3 && Math.random() < 0.7 ? starts : C);
    const opts = C.filter(c => c !== s && (() => { const d = Math.hypot(c.E - s.E, c.N - s.N); return d >= dmin && d <= dmax; })());
    if (!opts.length) continue;
    const t = rnd(opts);
    const route = idealRoute(s, t);
    if (!route) continue;
    const ev = evalPath(route), straight = Math.hypot(t.E - s.E, t.N - s.N);
    if (ev.dist > straight * 1.9) continue;
    return { s, t, route };
  }
  // גיבוי: שתי נקודות אקראיות
  const s = { E: T.e0 + T.size * 0.35, N: T.n0 + T.size * 0.35, desc: '' }, t = { E: T.e0 + T.size * 0.6, N: T.n0 + T.size * 0.55, desc: 'נקודה בשטח' };
  return { s, t, route: idealRoute(s, t) };
}

function newMission() {
  const { s, t, route } = pickMission();
  Object.assign(G, {
    start: { E: s.E, N: s.N }, target: { E: t.E, N: t.N }, targetDesc: t.desc,
    pos: { E: s.E, N: s.N }, hd: Math.floor(Math.random() * 360), drift: 0,
    paces: 0, legPaces: 0, walked: 0, time: 0, path: [{ E: s.E, N: s.N }], ideal: route,
    targetKnown: G.lv.targetShown, dotTries: 0, dotErr: null, dotMiss: null,
    marks: [], ruler: [], gps: 0, gpsUntil: 0, guess: null,
    bearings: [], backLines: [], pendingBearing: null,
    phase: G.lv.targetShown ? 'nav' : 'dot', done: {}, oriented: false, everOriented: false,
  });
  if (G.lv.targetShown) G.done.dot = true;
  $('orientLock').checked = false;
  $('mRegion').textContent = T.meta.name;
  $('mLevel').textContent = G.lv.name;
  $('mStart').textContent = fmtNZ(G.start.E, G.start.N);
  $('mTarget').textContent = fmtNZ(G.target.E, G.target.N);
  $('mTargetDesc').textContent = t.desc ? '· ' + t.desc : '';
  $('results').classList.add('hidden');
  $('results').innerHTML = '';
  $('toolRuler').classList.toggle('hidden', !G.lv.ruler);
  $('toolDot').classList.toggle('hidden', G.lv.targetShown);
  $('meterBox').classList.toggle('hidden', !G.lv.meters);
  $('cursorOut').textContent = '';
  $('rulerOut').textContent = '';
  $('bearOut').textContent = '💡 לחצו על נקודה בשטח (למשל פסגה) כדי לקחת אליה אזימוט.';
  $('backBtn').classList.add('hidden');
  $('optContours').checked = VIEWOPT.contours = G.level !== 'hard';
  $('optPeaks').checked = VIEWOPT.peaks = G.level === 'easy';
  setControlsEnabled(true);
  MV.rot = 0;
  fitMap(G.start, 1.6);
  setTool(G.phase === 'dot' ? 'dot' : 'pan');
  mapMsg(G.phase === 'dot'
    ? `📍 שלב 1: דקרו על המפה את נקודת היעד — נ״צ ${fmtNZ(G.target.E, G.target.N)} (מזרחית / צפונית).`
    : '🧭 היעד מסומן במפה ב־◎. מדדו אזימוט ומרחק, הצפינו את המפה וצאו לדרך.');
  fieldMsg('אתם עומדים בנקודת המוצא ▲. הסתכלו סביב (⟲ ⟳) והשוו את מה שאתם רואים למפה.', '');
  updateHUD(); renderView(); drawMap(); updateChecklist();
}

/* =======================================================================
   5. מבט בשטח — raycasting על רשת הגובה
   ======================================================================= */
const VW = 800, VH = 450;
const rv = document.createElement('canvas'); rv.width = VW; rv.height = VH;
const rctx = rv.getContext('2d');
const rimg = rctx.createImageData(VW, VH), rbuf = new Uint32Array(rimg.data.buffer);
const pack = (r, g, b) => (255 << 24) | ((b & 255) << 16) | ((g & 255) << 8) | (r & 255);
// הכהיית פיקסל ארוז לכיוון צבע נתון (לקווי רכס וקווי גובה)
const tint = (c, r, g, b, a) => pack((c & 255) * (1 - a) + r * a, ((c >>> 8) & 255) * (1 - a) + g * a, ((c >>> 16) & 255) * (1 - a) + b * a);

const PAL = {
  north:  { ground: [124, 140, 74], veg: [60, 88, 46], tree: [40, 66, 34], rock: [146, 138, 118], wet: [74, 108, 56], haze: [196, 208, 220], hz: 3400, skyTop: [96, 150, 212], skyLow: [208, 222, 234] },
  center: { ground: [170, 152, 112], veg: [100, 112, 62], tree: [66, 84, 44], rock: [190, 180, 158], wet: [122, 124, 82], haze: [204, 208, 214], hz: 3800, skyTop: [104, 156, 214], skyLow: [214, 224, 232] },
  desert: { ground: [208, 174, 126], veg: [150, 130, 90], tree: [110, 104, 70], rock: [166, 124, 90], wet: [232, 218, 186], haze: [224, 212, 198], hz: 5200, skyTop: [112, 162, 214], skyLow: [230, 224, 212] },
};
// שכבות עזר במבט בשטח
const VIEWOPT = { contours: false, peaks: false };
let viewLabels = [];          // נקודות גובה שנראות בשטח: {b: אזימוט רשת, d, z}
let viewEyeZ = 0;

function renderView() {
  if (!T) return;
  const P = PAL[T.meta.biome], f = (VW / 2) / Math.tan(rad(FOV / 2)), y0 = Math.round(VH * 0.46);
  const { nx, ny, cell, e0, n0, h, shade, slope, wet } = T, vth = VEG_TH[T.meta.biome];
  const eyeZ = hAt(G.pos.E, G.pos.N) + EYE; viewEyeZ = eyeZ;
  const sky = new Uint32Array(VH);
  for (let y = 0; y < VH; y++) {
    const t = clamp(y / y0, 0, 1);
    sky[y] = pack(P.skyTop[0] + (P.skyLow[0] - P.skyTop[0]) * t, P.skyTop[1] + (P.skyLow[1] - P.skyTop[1]) * t, P.skyTop[2] + (P.skyLow[2] - P.skyTop[2]) * t);
  }
  const hd = rad(G.hd), cont = VIEWOPT.contours;
  for (let x = 0; x < VW; x++) {
    const off = Math.atan((x + 0.5 - VW / 2) / f), a = hd + off, sa = Math.sin(a), ca = Math.cos(a), corr = Math.cos(off);
    let ybuf = VH, d = 1.5, lastD = 0, prevZ = NaN;
    while (d < 7000 && ybuf > 0) {
      const E = G.pos.E + sa * d, N = G.pos.N + ca * d;
      let gx = (E - e0) / cell, gy = (N - n0) / cell, over = 0;
      if (gx < 0) { over = -gx; gx = 0; } else if (gx > nx - 1.001) { over = gx - nx + 1.001; gx = nx - 1.001; }
      if (gy < 0) { over = Math.max(over, -gy); gy = 0; } else if (gy > ny - 1.001) { over = Math.max(over, gy - ny + 1.001); gy = ny - 1.001; }
      const i = gx | 0, j = gy | 0, fx = gx - i, fy = gy - j, k = j * nx + i;
      const w00 = (1 - fx) * (1 - fy), w10 = fx * (1 - fy), w01 = (1 - fx) * fy, w11 = fx * fy;
      const zg = h[k] * w00 + h[k + 1] * w10 + h[k + nx] * w01 + h[k + nx + 1] * w11;
      let z = zg;
      if (over) z -= over * cell * 0.4;   // מעבר לגבול הגזרה השטח "צונח" אל האופק
      const sl = slope[k] * w00 + slope[k + 1] * w10 + slope[k + nx] * w01 + slope[k + nx + 1] * w11;
      // עצים בודדים בחורש הקרוב — נותנים קנה מידה ותחושת תנועה
      let tree = 0, tv = -1;
      if (vth < 1 && d < 240 && sl < 0.6) {
        tv = clamp((vegIndex(E, N) - vth) / 0.05, 0, 1);
        if (tv > 0.5) {
          const cx = Math.floor(E / 7), cy = Math.floor(N / 7);
          if (hash2(cx, cy) > 0.42) {
            const ox = (cx + 0.2 + 0.6 * hash2(cy, cx)) * 7, oy = (cy + 0.2 + 0.6 * hash2(cx + 7, cy - 3)) * 7, r = Math.hypot(E - ox, N - oy);
            if (r < 2.8) { tree = 1.5 + 4 * (1 - (r / 2.8) ** 2) * (0.7 + 0.6 * hash2(cx - 5, cy + 9)); z += tree; }
          }
        }
      }
      const sy = y0 - (z - eyeZ) * f / (d * corr);
      if (sy < ybuf) {
        const top = Math.max(0, Math.ceil(sy));
        if (top < ybuf) {
          const sh = shade[k] * w00 + shade[k + 1] * w10 + shade[k + nx] * w01 + shade[k + nx + 1] * w11;
          let c;
          if (tree) c = P.tree;
          else {
            if (tv < 0) tv = vth < 1 ? clamp((vegIndex(E, N) - vth) / 0.05, 0, 1) * clamp((0.6 - sl) / 0.1, 0, 1) : 0;
            const tr = clamp((sl - 0.45) / 0.3, 0, 1);
            const tw = clamp((wet[k] * w00 + wet[k + 1] * w10 + wet[k + nx] * w01 + wet[k + nx + 1] * w11) * 1.4, 0, 1) * (1 - tr);
            c = [0, 1, 2].map(q => ((P.ground[q] * (1 - tv) + P.veg[q] * tv) * (1 - tr) + P.rock[q] * tr) * (1 - tw) + P.wet[q] * tw);
          }
          let lum = 0.36 + 0.86 * sh;
          if (d < 400 && !tree) lum *= 0.9 + 0.2 * vnoise(E / 3.1, N / 3.1) * (1 - d / 400) + 0.1 * (d / 400);
          const t = 1 - Math.exp(-d / P.hz);
          let col = pack(
            c[0] * lum * (1 - t) + P.haze[0] * t,
            c[1] * lum * (1 - t) + P.haze[1] * t,
            c[2] * lum * (1 - t) + P.haze[2] * t);
          // קווי גובה בשטח (עזר): כל 10 מ׳, מודגש כל 50 מ׳
          if (cont && d < 2500 && prevZ === prevZ && Math.floor(zg / 10) !== Math.floor(prevZ / 10)) {
            const idx = (Math.floor(Math.max(zg, prevZ) / 10) * 10) % 50 === 0;
            col = tint(col, 110, 62, 20, (idx ? 0.85 : 0.5) * (1 - d / 2500));
          }
          // קו רכס: כשמאחורי תוואי קרוב מופיע שטח רחוק — מודגש קו המתאר של הקרוב
          if (lastD && ybuf < VH && d > lastD * 1.3 + 25) {
            const al = clamp(1 - lastD / 3500, 0.3, 0.85);
            rbuf[ybuf * VW + x] = tint(rbuf[ybuf * VW + x], 30, 34, 24, al);
            if (ybuf + 1 < VH && lastD < 1200) rbuf[(ybuf + 1) * VW + x] = tint(rbuf[(ybuf + 1) * VW + x], 30, 34, 24, al * 0.5);
          }
          for (let y = top; y < ybuf; y++) rbuf[y * VW + x] = col;
          ybuf = top; lastD = d;
        }
      }
      prevZ = zg;
      d += 0.5 + d * 0.009;
    }
    if (ybuf < VH && ybuf > 0) rbuf[ybuf * VW + x] = tint(rbuf[ybuf * VW + x], 40, 46, 36, 0.45);   // קו האופק
    for (let y = 0; y < ybuf; y++) rbuf[y * VW + x] = sky[y];
  }
  rctx.putImageData(rimg, 0, 0);

  // נקודות גובה שנראות מכאן (בדיקת הסתרה לאורך הקו)
  viewLabels = [];
  if (VIEWOPT.peaks) {
    for (const [i, j, z] of T.meta.peaks) {
      const E = T.e0 + i * cell, N = T.n0 + j * cell, dist = Math.hypot(E - G.pos.E, N - G.pos.N);
      if (dist < 60 || dist > 6500) continue;
      const b = azimuth(E - G.pos.E, N - G.pos.N);
      if (Math.abs(angDiff(b, G.hd)) > FOV / 2 + 2) continue;
      const ang = (z - eyeZ) / dist, sb = Math.sin(rad(b)), cb = Math.cos(rad(b));
      let vis = true;
      for (let s = 30; s < dist - 50; s += Math.max(15, s * 0.03)) {
        if ((hAt(G.pos.E + sb * s, G.pos.N + cb * s) - eyeZ) / s > ang + 0.004) { vis = false; break; }
      }
      if (vis) viewLabels.push({ b, d: dist, z });
    }
  }
  drawView();
}

// הצגת המבט + שכבת מצפן (HUD) ברזולוציית המסך
let viewHover = null;   // x של העכבר מעל המבט
function viewProj(W) { return (W / 2) / Math.tan(rad(FOV / 2)); }
function drawView() {
  const cv = $('viewCv'), dpr = window.devicePixelRatio || 1;
  const W = cv.clientWidth, H = cv.clientHeight;
  if (!W || !H) return;
  if (cv.width !== Math.round(W * dpr)) { cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr); }
  const ctx = cv.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.imageSmoothingEnabled = true;
  ctx.drawImage(rv, 0, 0, W, H);

  const mag = norm360(G.hd - DECL), f = viewProj(W), y0 = H * 0.46;
  const xOfMag = b => W / 2 + Math.tan(rad(angDiff(b, mag))) * f;   // x של אזימוט מגנטי
  const halo = (txt, x, y, color, font) => {
    ctx.font = font; ctx.lineWidth = 3.5; ctx.strokeStyle = 'rgba(255,255,255,0.92)'; ctx.strokeText(txt, x, y); ctx.fillStyle = color; ctx.fillText(txt, x, y);
  };

  // נקודות גובה בשטח (עזר)
  ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
  const placed = [];
  for (const p of [...viewLabels].sort((a, b) => a.d - b.d)) {
    const rel = angDiff(p.b, G.hd), x = W / 2 + Math.tan(rad(rel)) * f;
    const y = y0 - (p.z - viewEyeZ) * f / (p.d * Math.cos(rad(rel)));
    if (placed.some(q => Math.abs(q[0] - x) < 46 && Math.abs(q[1] - y) < 30)) continue;   // בלי תוויות חופפות
    placed.push([x, y]);
    ctx.fillStyle = '#111'; ctx.beginPath(); ctx.moveTo(x, y - 9); ctx.lineTo(x + 5, y - 2); ctx.lineTo(x - 5, y - 2); ctx.closePath(); ctx.fill();
    halo(`${p.z}`, x, y - 11, '#111', '800 12px Heebo, sans-serif');
    halo(fmtDist(p.d), x, y - 25, '#444', '600 10px Heebo, sans-serif');
  }

  // אזימוטים שנלקחו לנקודות בשטח
  for (const br of G.bearings) {
    if (Math.abs(angDiff(br.mag, mag)) > FOV / 2) continue;
    const x = xOfMag(br.mag);
    ctx.strokeStyle = '#7a1fa0'; ctx.lineWidth = 2; ctx.setLineDash([6, 4]);
    ctx.beginPath(); ctx.moveTo(x, 40); ctx.lineTo(x, H * 0.8); ctx.stroke(); ctx.setLineDash([]);
    ctx.textBaseline = 'top'; halo(`${Math.round(br.mag)}° (${br.n})`, x, H * 0.8 + 3, '#7a1fa0', '800 12px Heebo, sans-serif');
  }
  // עכבר מעל המבט: אזימוט חי
  if (viewHover !== null && G.phase !== 'done') {
    const b = norm360(mag + deg(Math.atan((viewHover - W / 2) / f)));
    ctx.strokeStyle = 'rgba(255,255,255,0.8)'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(viewHover, 40); ctx.lineTo(viewHover, H - 8); ctx.stroke();
    ctx.textBaseline = 'top'; halo(`${Math.round(b)}°`, viewHover, 54, '#7a1fa0', '800 13px Heebo, sans-serif');
  }

  // סרט מצפן עליון — זוויות פרספקטיביות, כך שאפשר "לקחת אזימוט" לפסגה שנראית
  ctx.fillStyle = 'rgba(20,26,12,0.62)'; ctx.fillRect(0, 0, W, 36);
  ctx.strokeStyle = '#efe7d0'; ctx.fillStyle = '#efe7d0'; ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  const CARD = { 0: 'צ', 90: 'מז', 180: 'ד', 270: 'מע' };
  for (let b = Math.floor(mag - FOV / 2 - 5); b <= mag + FOV / 2 + 5; b++) {
    const bb = norm360(b); if (bb % 5) continue;
    const x = W / 2 + Math.tan(rad(b - mag)) * f;
    if (x < 0 || x > W) continue;
    const big = bb % 10 === 0;
    ctx.strokeStyle = '#efe7d0'; ctx.lineWidth = big ? 1.6 : 1; ctx.beginPath(); ctx.moveTo(x, 36); ctx.lineTo(x, big ? 26 : 30); ctx.stroke();
    if (bb % 10 === 0) {
      ctx.font = CARD[bb] !== undefined ? '800 13px Heebo, sans-serif' : '600 11px Heebo, sans-serif';
      ctx.fillStyle = CARD[bb] !== undefined ? '#ffcf5a' : '#efe7d0';
      ctx.fillText(CARD[bb] !== undefined ? CARD[bb] : String(bb), x, 6);
    }
  }
  ctx.fillStyle = '#e04a2a';
  ctx.beginPath(); ctx.moveTo(W / 2, 40); ctx.lineTo(W / 2 - 7, 50); ctx.lineTo(W / 2 + 7, 50); ctx.closePath(); ctx.fill();
  // קו כיוונון במרכז
  ctx.strokeStyle = 'rgba(224,74,42,0.75)'; ctx.lineWidth = 1.2; ctx.setLineDash([4, 4]);
  ctx.beginPath(); ctx.moveTo(W / 2, 52); ctx.lineTo(W / 2, H * 0.62); ctx.stroke(); ctx.setLineDash([]);

  // מצפן קטן: המחט מצביעה לצפון המגנטי ביחס לכיוון המבט
  const cx = 46, cy = H - 46, R = 34;
  ctx.fillStyle = 'rgba(239,231,208,0.92)'; ctx.strokeStyle = '#26301c'; ctx.lineWidth = 2;
  ctx.beginPath(); ctx.arc(cx, cy, R, 0, TAU); ctx.fill(); ctx.stroke();
  ctx.fillStyle = '#26301c'; ctx.font = '700 10px Heebo, sans-serif'; ctx.textBaseline = 'middle';
  ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(239,231,208,0.9)'; ctx.strokeText('מבט ↑', cx, cy - R - 8); ctx.fillText('מבט ↑', cx, cy - R - 8);
  const na = rad(-mag);
  ctx.save(); ctx.translate(cx, cy); ctx.rotate(na);
  ctx.fillStyle = '#c0392b'; ctx.beginPath(); ctx.moveTo(0, -R + 15); ctx.lineTo(5, 0); ctx.lineTo(-5, 0); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#eee'; ctx.strokeStyle = '#26301c'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(0, R - 15); ctx.lineTo(5, 0); ctx.lineTo(-5, 0); ctx.closePath(); ctx.fill(); ctx.stroke();
  ctx.fillStyle = '#c0392b'; ctx.font = '800 11px Heebo, sans-serif'; ctx.fillText('צ', 0, -R + 8);
  ctx.restore();
}

/* ---------- לקיחת אזימוט לנקודה בשטח (לחיצה על המבט) ---------- */
(() => {
  const cv = $('viewCv');
  cv.addEventListener('pointermove', e => { if (e.pointerType === 'mouse' && T && G.phase !== 'idle') { viewHover = e.offsetX; drawView(); } });
  cv.addEventListener('pointerleave', () => { viewHover = null; if (T && G.phase !== 'idle') drawView(); });
  cv.addEventListener('click', e => {
    if (!T || G.phase === 'idle' || G.phase === 'done') return;
    const W = cv.clientWidth, mag = norm360(G.hd - DECL + deg(Math.atan((e.offsetX - W / 2) / viewProj(W))));
    if (G.bearings.length >= 4) G.bearings.shift();
    const n = (G.bearingSeq = (G.bearingSeq || 0) + 1);
    G.bearings.push({ mag, n });
    G.pendingBearing = G.bearings[G.bearings.length - 1];
    $('bearOut').innerHTML = `🎯 אזימוט ${n} לנקודה בשטח: <b>${Math.round(mag)}°</b> מגנטי (חוזר: ${Math.round(norm360(mag + 180))}°)`;
    $('backBtn').classList.remove('hidden');
    drawView();
  });
})();

/* =======================================================================
   6. תנועה בשטח
   ======================================================================= */
let walking = null;    // {left: צעדים שנותרו} או {hold:true}

function stepOnce() {
  const az = G.hd + (G.lv.drift ? G.drift : 0);
  const g = gradeAlong(G.pos.E, G.pos.N, az);
  if (Math.abs(g) > MAXG) {
    fieldMsg(g > 0 ? '⛔ המדרון לפניכם תלול מדי (מצוק) — אי אפשר לטפס כאן. חפשו מעבר אחר.' : '⛔ לפניכם מצוק — אי אפשר לרדת כאן. חפשו מעבר אחר.', 'bad');
    return false;
  }
  const s = strideFor(g), E = G.pos.E + Math.sin(rad(az)) * s, N = G.pos.N + Math.cos(rad(az)) * s;
  if (!inside(E, N, 60)) { fieldMsg('⛔ הגעתם לגבול הגזרה (קצה המפה).', 'bad'); return false; }
  const dz = hAt(E, N) - hAt(G.pos.E, G.pos.N);
  G.time += Math.hypot(s, dz) / tobler(dz / s);
  G.pos = { E, N }; G.paces++; G.legPaces++; G.walked += s;
  if (G.lv.drift) G.drift = clamp(G.drift + (Math.random() - 0.5) * 0.5, -4, 4);
  const last = G.path[G.path.length - 1];
  if (Math.hypot(E - last.E, N - last.N) > 8) G.path.push({ E, N });
  return true;
}

const HOLD_RATE = 18;   // צמדי צעדים לשנייה בהליכה רציפה
function walkTick(now) {
  if (!walking) return;
  let n;
  if (walking.hold) {
    walking.acc = (walking.acc || 0) + Math.min(0.1, (now - (walking.t || now)) / 1000) * HOLD_RATE;
    walking.t = now; n = Math.floor(walking.acc); walking.acc -= n;
    if (!n) { requestAnimationFrame(walkTick); return; }
  } else n = Math.min(walking.left, 4);
  let ok = true;
  for (let q = 0; q < n && ok; q++) ok = stepOnce();
  if (!walking.hold) walking.left -= n;
  if (!G.done.walk && G.paces > 0) { G.done.walk = true; updateChecklist(); }
  updateHUD(); renderView(); drawMap();
  if (!ok || (!walking.hold && walking.left <= 0)) { stopWalk(); return; }
  requestAnimationFrame(walkTick);
}
function startWalk(paces) {
  if (G.phase !== 'nav' && G.phase !== 'dot') return;
  if (walking) return;
  fieldMsg('', '');
  walking = paces ? { left: paces } : { hold: true };
  $('holdWalk').classList.toggle('active', !paces);
  requestAnimationFrame(walkTick);
}
function stopWalk() { walking = null; $('holdWalk').classList.remove('active'); }

function turn(dd) {
  if (G.phase === 'done' || G.phase === 'idle') return;
  G.hd = norm360(G.hd + dd);
  updateHUD(); renderView();
  if (lockOrient()) drawMap(); else updateOrient();
}

function updateHUD() {
  const mag = norm360(G.hd - DECL);
  $('hdOut').textContent = String(Math.round(mag) % 360).padStart(3, '0') + '°';
  $('paceOut').textContent = G.legPaces.toLocaleString('he-IL');
  $('meterOut').textContent = fmtDist(G.walked);
  $('mClock').textContent = fmtTime(G.time);
  $('mGps').textContent = G.gps;
  const g = gradeAlong(G.pos.E, G.pos.N, G.hd) * 100;
  $('slopeOut').textContent = Math.abs(g) < 3 ? 'מישור' : (g > 0 ? `עלייה ${Math.round(g)}%` : `ירידה ${Math.round(-g)}%`) + (Math.abs(g) > MAXG * 100 ? ' ⛔' : '');
}

/* =======================================================================
   7. המפה — תצוגה, סיבוב, זום וכלים
   ======================================================================= */
const MV = { cx: 0, cy: 0, z: 0.1, rot: 0 };
const mapCv = $('mapCv');

function mapSize() { return { W: mapCv.clientWidth, H: mapCv.clientHeight }; }
function w2s(E, N) {
  const { W, H } = mapSize(), dx = (E - MV.cx) * MV.z, dy = -(N - MV.cy) * MV.z, r = rad(MV.rot);
  return [W / 2 + dx * Math.cos(r) - dy * Math.sin(r), H / 2 + dx * Math.sin(r) + dy * Math.cos(r)];
}
function s2w(x, y) {
  const { W, H } = mapSize(), r = rad(-MV.rot), dx = x - W / 2, dy = y - H / 2;
  const ux = dx * Math.cos(r) - dy * Math.sin(r), uy = dx * Math.sin(r) + dy * Math.cos(r);
  return { E: MV.cx + ux / MV.z, N: MV.cy - uy / MV.z };
}
function fitMap(center, kmAcross) {
  const { W, H } = mapSize();
  MV.z = Math.min(W, H) / (kmAcross * 1000);
  MV.cx = center.E; MV.cy = center.N;
  clampView();
}
function clampView() {
  const { W, H } = mapSize();
  MV.z = clamp(MV.z, Math.min(W, H) / (T.size * 1.15), 1.2);
  MV.cx = clamp(MV.cx, T.e0, T.e0 + T.size); MV.cy = clamp(MV.cy, T.n0, T.nTop);
}

function drawMap() {
  if (!T || !mapBase) return;
  const dpr = window.devicePixelRatio || 1, { W, H } = mapSize();
  if (!W) return;
  if (mapCv.width !== Math.round(W * dpr) || mapCv.height !== Math.round(H * dpr)) { mapCv.width = Math.round(W * dpr); mapCv.height = Math.round(H * dpr); }
  const ctx = mapCv.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.fillStyle = '#d8d2bf'; ctx.fillRect(0, 0, W, H);
  ctx.save();
  ctx.translate(W / 2, H / 2); ctx.rotate(rad(MV.rot)); ctx.scale(MV.z / MPX, MV.z / MPX);
  ctx.translate(-bx(MV.cx), -by(MV.cy));
  ctx.imageSmoothingEnabled = true;
  ctx.drawImage(mapBase, 0, 0);
  ctx.restore();

  const line = (pts, color, w, dash) => {
    if (!pts || pts.length < 2) return;
    ctx.strokeStyle = color; ctx.lineWidth = w; ctx.setLineDash(dash || []); ctx.lineJoin = ctx.lineCap = 'round';
    ctx.beginPath(); pts.forEach((p, k) => { const [x, y] = w2s(p.E, p.N); k ? ctx.lineTo(x, y) : ctx.moveTo(x, y); }); ctx.stroke(); ctx.setLineDash([]);
  };
  const label = (txt, x, y, color) => {
    ctx.font = '800 12px Heebo, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.lineWidth = 3.5; ctx.strokeStyle = 'rgba(255,255,255,0.95)'; ctx.strokeText(txt, x, y); ctx.fillStyle = color; ctx.fillText(txt, x, y);
  };

  // תוצאות: מסלולים
  if (G.phase === 'done') {
    line([G.start, G.target], 'rgba(60,60,60,0.75)', 1.5, [3, 5]);
    if (G.ideal) line(G.ideal, '#1f8a3a', 4, [10, 6]);
    line(G.path.concat([G.pos]), '#d0342c', 3);
  }

  // סרגל
  // קווים חוזרים (חיתוך לאחור)
  for (const bl of G.backLines) {
    const far = { E: bl.E + Math.sin(rad(bl.az)) * 5000, N: bl.N + Math.cos(rad(bl.az)) * 5000 };
    line([bl, far], '#7a1fa0', 2, [9, 5]);
    const [x, y] = w2s(bl.E, bl.N); ctx.fillStyle = '#7a1fa0'; ctx.beginPath(); ctx.arc(x, y, 4, 0, TAU); ctx.fill();
    const [lx, ly] = w2s(bl.E + Math.sin(rad(bl.az)) * 300, bl.N + Math.cos(rad(bl.az)) * 300);
    label(`חוזר ${bl.n}: ${Math.round(bl.az)}°`, lx, ly, '#7a1fa0');
  }
  // מד־זווית: עיגול מעלות סביב הנקודה הראשונה (מיושר לצפון הרשת) + קו ומדידה
  if (G.ruler.length) {
    const [a, b] = G.ruler, [ax, ay] = w2s(a.E, a.N), R = 80;
    ctx.save(); ctx.translate(ax, ay);
    ctx.fillStyle = 'rgba(255,255,255,0.6)'; ctx.strokeStyle = '#7a1fa0'; ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.arc(0, 0, R, 0, TAU); ctx.fill(); ctx.stroke();
    ctx.font = '700 10px Heebo, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillStyle = '#5a1678';
    for (let t = 0; t < 360; t += 5) {
      const q = rad(t + MV.rot), sx = Math.sin(q), sy = -Math.cos(q), l = t % 30 === 0 ? 13 : t % 10 === 0 ? 8 : 4;
      ctx.lineWidth = t % 30 === 0 ? 1.8 : 1;
      ctx.beginPath(); ctx.moveTo(sx * R, sy * R); ctx.lineTo(sx * (R - l), sy * (R - l)); ctx.stroke();
      if (t % 30 === 0) ctx.fillText(t === 0 ? 'צ' : String(t), sx * (R - 22), sy * (R - 22));
    }
    ctx.restore();
    if (b) {
      const az = azimuth(b.E - a.E, b.N - a.N), dist = Math.hypot(b.E - a.E, b.N - a.N);
      // קשת הזווית מצפון הרשת לקו
      ctx.strokeStyle = 'rgba(122,31,160,0.85)'; ctx.lineWidth = 3;
      ctx.beginPath(); ctx.arc(ax, ay, 30, rad(MV.rot - 90), rad(MV.rot + az - 90)); ctx.stroke();
      const nq = rad(MV.rot); ctx.lineWidth = 1.5; ctx.setLineDash([3, 3]);
      ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(ax + Math.sin(nq) * R, ay - Math.cos(nq) * R); ctx.stroke(); ctx.setLineDash([]);
      line([a, b], '#7a1fa0', 2.6);
      const [x2, y2] = w2s(b.E, b.N); ctx.fillStyle = '#7a1fa0'; ctx.beginPath(); ctx.arc(x2, y2, 4.5, 0, TAU); ctx.fill();
      const q = rad(az + MV.rot), mx = (ax + x2) / 2 + Math.cos(q) * 16, my = (ay + y2) / 2 + Math.sin(q) * 16;
      label(`${Math.round(az)}° · ${fmtDist(dist)}`, mx, my, '#5a1678');
    }
    ctx.fillStyle = '#7a1fa0'; ctx.beginPath(); ctx.arc(ax, ay, 4.5, 0, TAU); ctx.fill();
  }
  // סימונים ✏️
  G.marks.forEach((m, k) => {
    const [x, y] = w2s(m.E, m.N);
    ctx.strokeStyle = '#0d5f8a'; ctx.lineWidth = 2.5;
    ctx.beginPath(); ctx.moveTo(x - 6, y - 6); ctx.lineTo(x + 6, y + 6); ctx.moveTo(x + 6, y - 6); ctx.lineTo(x - 6, y + 6); ctx.stroke();
    label(String(k + 1), x + 11, y - 9, '#0d5f8a');
  });
  // מוצא ▲
  { const [x, y] = w2s(G.start.E, G.start.N);
    ctx.fillStyle = '#d0342c'; ctx.strokeStyle = '#fff'; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(x, y - 10); ctx.lineTo(x + 9, y + 6); ctx.lineTo(x - 9, y + 6); ctx.closePath(); ctx.fill(); ctx.stroke();
    label('מוצא', x, y + 17, '#d0342c'); }
  // יעד ◎
  if (G.targetKnown || G.phase === 'done') {
    const [x, y] = w2s(G.target.E, G.target.N);
    ctx.strokeStyle = '#d0342c'; ctx.lineWidth = 2.5;
    ctx.beginPath(); ctx.arc(x, y, 11, 0, TAU); ctx.stroke();
    ctx.fillStyle = '#d0342c'; ctx.beginPath(); ctx.arc(x, y, 2.5, 0, TAU); ctx.fill();
    label('יעד', x, y - 19, '#d0342c');
  }
  // ניסיון דקירה שגוי
  if (G.dotMiss) { const [x, y] = w2s(G.dotMiss.E, G.dotMiss.N); ctx.fillStyle = 'rgba(208,52,44,0.6)'; ctx.beginPath(); ctx.arc(x, y, 5, 0, TAU); ctx.fill(); }
  // דקירת מיקום סופי
  if (G.guess) {
    const [x, y] = w2s(G.guess.E, G.guess.N);
    ctx.strokeStyle = '#0d5f8a'; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(x, y, 8, 0, TAU); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(x - 13, y); ctx.lineTo(x + 13, y); ctx.moveTo(x, y - 13); ctx.lineTo(x, y + 13); ctx.stroke();
    label('הדקירה שלי', x, y + 22, '#0d5f8a');
  }
  // מיקום אמיתי — רק ב־GPS או בסוף
  if (G.phase === 'done' || performance.now() < G.gpsUntil) {
    const [x, y] = w2s(G.pos.E, G.pos.N);
    ctx.fillStyle = '#ff7a00'; ctx.strokeStyle = '#fff'; ctx.lineWidth = 2.5;
    ctx.beginPath(); ctx.arc(x, y, 7, 0, TAU); ctx.fill(); ctx.stroke();
    // כיוון מבט
    const a = rad(G.hd + MV.rot);
    ctx.strokeStyle = '#ff7a00'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(x + Math.sin(a) * 22, y - Math.cos(a) * 22); ctx.stroke();
    label(G.phase === 'done' ? 'המיקום האמיתי' : 'GPS', x, y - 18, '#c45a00');
  }

  // חץ צפון (מסתובב עם המפה)
  { const x = 34, y = H - 34, a = rad(MV.rot);
    ctx.save(); ctx.translate(x, y); ctx.rotate(a);
    ctx.fillStyle = 'rgba(255,255,255,0.85)'; ctx.beginPath(); ctx.arc(0, 0, 22, 0, TAU); ctx.fill();
    ctx.fillStyle = '#1f4fa0'; ctx.beginPath(); ctx.moveTo(0, -18); ctx.lineTo(7, 6); ctx.lineTo(0, 1); ctx.lineTo(-7, 6); ctx.closePath(); ctx.fill();
    ctx.font = '800 11px Heebo, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText('צ', 0, 13);
    ctx.restore(); }
  // סרגל קנה מידה
  { const target = 110 / MV.z, pow = Math.pow(10, Math.floor(Math.log10(target)));
    const len = [1, 2, 5, 10].map(m => m * pow).filter(v => v <= target).pop() || pow, px = len * MV.z;
    const x0 = W - 20 - px, y0 = H - 18;
    ctx.fillStyle = 'rgba(255,255,255,0.85)'; ctx.fillRect(x0 - 8, y0 - 18, px + 16, 26);
    ctx.fillStyle = '#222'; ctx.fillRect(x0, y0 - 3, px, 5); ctx.fillStyle = '#fff'; ctx.fillRect(x0 + px / 2, y0 - 2, px / 2 - 1, 3);
    ctx.fillStyle = '#222'; ctx.font = '700 11px Heebo, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
    ctx.fillText(len >= 1000 ? len / 1000 + ' ק״מ' : len + ' מ׳', x0 + px / 2, y0 - 4); }
  updateOrient();
}

/* ---------- הצפנת מפה ---------- */
function updateOrient() {
  const err = angDiff(MV.rot, -G.hd);
  G.oriented = Math.abs(err) <= 10;
  if (G.oriented && !G.everOriented && G.phase !== 'done') { G.everOriented = true; G.done.orient = true; updateChecklist(); }
  const el = $('orientOut');
  el.classList.toggle('ok', G.oriented);
  el.textContent = G.oriented ? `✓ המפה מוצפנת (סטייה ${Math.abs(Math.round(err))}°)` : 'המפה לא מוצפנת — סובבו אותה עד שהצפון שלה מתיישר עם מחט המצפן';
}
function lockOrient() {
  if (!$('orientLock').checked) return false;
  MV.rot = norm360(-G.hd); return true;
}
function rotateMap(dd) { $('orientLock').checked = false; MV.rot = norm360(MV.rot + dd); drawMap(); }

/* ---------- כלים ---------- */
function setTool(t) {
  G.tool = t;
  document.querySelectorAll('#mapTools .tool').forEach(b => b.classList.toggle('on', b.dataset.tool === t));
  mapCv.classList.toggle('crosshair', t !== 'pan');
}
function mapMsg(txt) { const el = $('mapMsg'); el.textContent = txt || ''; el.classList.toggle('hidden', !txt); }
function fieldMsg(txt, cls) { const el = $('fieldMsg'); el.textContent = txt; el.className = 'feedback' + (cls ? ' ' + cls : ''); }

function onMapTap(x, y) {
  const p = s2w(x, y);
  if (!inside(p.E, p.N)) return;
  if (G.phase === 'final') {
    G.guess = p; drawMap();
    mapMsg('🏁 זו הדקירה שלכם? אפשר ללחוץ שוב לתיקון. כשאתם בטוחים — "אשר דקירה" למטה.');
    $('arriveBtn').textContent = '✅ אשר דקירה וסיים'; return;
  }
  if (G.tool === 'dot' && G.phase === 'dot') {
    const err = Math.hypot(p.E - G.target.E, p.N - G.target.N);
    G.dotTries++;
    if (G.dotErr === null) G.dotErr = err;
    if (err <= 80) {
      G.targetKnown = true; G.phase = 'nav'; G.dotMiss = null; G.done.dot = true;
      mapMsg(`✓ דקירה מדויקת (שגיאה ${Math.round(err)} מ׳)! היעד מסומן ב־◎. עכשיו: אזימוט, מרחק, הצפנה — ויציאה לדרך.`);
      setTool(G.lv.ruler ? 'ruler' : 'pan'); updateChecklist();
    } else if (G.dotTries >= 3) {
      G.targetKnown = true; G.phase = 'nav'; G.dotMiss = null; G.done.dot = true;
      mapMsg(`✗ החטאה של ${Math.round(err)} מ׳. אחרי 3 ניסיונות היעד סומן עבורכם — בדקו איפה טעיתם (קודם מזרחית, אחר כך צפונית).`);
      setTool('pan'); updateChecklist();
    } else {
      G.dotMiss = p;
      const dE = G.target.E - p.E, dN = G.target.N - p.N;
      const hint = Math.abs(dE) > Math.abs(dN) ? (Math.abs(dE) > 400 ? 'בדקו שוב את המזרחית' : 'כמעט — דייקו את המזרחית') : (Math.abs(dN) > 400 ? 'בדקו שוב את הצפונית' : 'כמעט — דייקו את הצפונית');
      mapMsg(`✗ החטאה של ${Math.round(err)} מ׳ — ${hint}. נסו שוב (ניסיון ${G.dotTries} מתוך 3). נ״צ: ${fmtNZ(G.target.E, G.target.N)}`);
    }
    drawMap(); return;
  }
  if (G.tool === 'back' && G.pendingBearing) {
    const q = snapPt(p), br = G.pendingBearing, az = norm360(br.mag + DECL + 180);
    G.backLines = G.backLines.filter(l => l.n !== br.n).slice(-3);
    G.backLines.push({ E: q.E, N: q.N, az, n: br.n });
    G.pendingBearing = null; $('backBtn').classList.add('hidden'); setTool('pan');
    mapMsg(G.backLines.length >= 2
      ? '🎯 שני קווים חוזרים או יותר: המיקום שלכם בערך בנקודת ההצטלבות שלהם. סמנו אותו ב־✏️.'
      : `🎯 שורטט קו חוזר (אזימוט רשת ${Math.round(az)}°). אתם נמצאים איפשהו עליו. קחו אזימוט לתוואי נוסף כדי לקבל הצטלבות.`);
    drawMap(); return;
  }
  if (G.tool === 'mark' && G.phase !== 'done') {
    if (G.marks.length >= 12) G.marks.shift();
    G.marks.push(p); G.done.mark = true; updateChecklist(); drawMap();
    const k = G.marks.length;
    fieldMsg(`✏️ סימון ${k} נשמר — בסוף תראו כמה הוא היה קרוב למיקום האמיתי שלכם באותו רגע.`, '');
    G.marks[k - 1].truth = { E: G.pos.E, N: G.pos.N };
  }
}

// הצמדה לנקודה ידועה קרובה (מוצא, יעד, סימונים, נקודות גובה)
function snapPt(p) {
  const pts = [G.start, ...(G.targetKnown ? [G.target] : []), ...G.marks,
    ...T.meta.peaks.map(([i, j]) => ({ E: T.e0 + i * T.cell, N: T.n0 + j * T.cell }))];
  let best = null, bd = 16 / MV.z;
  for (const q of pts) { const d = Math.hypot(q.E - p.E, q.N - p.N); if (d < bd) { bd = d; best = q; } }
  return best ? { E: best.E, N: best.N } : p;
}

function updateRuler() {
  const out = $('rulerOut');
  if (G.ruler.length < 2) { out.textContent = G.ruler.length ? '📐 לחצו או גררו אל הנקודה השנייה' : ''; return; }
  const [a, b] = G.ruler, dE = b.E - a.E, dN = b.N - a.N, grid = azimuth(dE, dN), dist = Math.hypot(dE, dN);
  const full = G.lv.ruler === 'full', mag = norm360(grid - DECL);
  out.innerHTML = `📐 אזימוט רשת <b>${Math.round(grid) % 360}°</b>` + (full ? ` · מגנטי <b>${Math.round(mag) % 360}°</b>` : ' <span class="small">(למצפן: פחות 4.9°)</span>') +
    ` · חוזר ${Math.round(norm360(grid + 180)) % 360}° · מרחק <b>${fmtDist(dist)}</b>` + (full ? ` (≈${Math.round(dist / PACE)} צמדי צעדים במישור)` : '') +
    (full ? ' <button class="gbtn tiny" id="rulerAim">🧭 כוונו את המצפן לאזימוט הזה</button>' : '');
  if (full) $('rulerAim').addEventListener('click', () => {
    if (G.phase === 'done' || G.phase === 'final') return;
    G.hd = norm360(grid); updateHUD(); renderView(); if (lockOrient()) drawMap(); else updateOrient();
    fieldMsg(`🧭 המצפן מכוון לאזימוט מגנטי ${Math.round(mag) % 360}°.`, '');
  });
  // נחשב "מדידת אזימוט" אם הסרגל נמתח בין סביבת נקודה ידועה ליעד
  const near = (p, q) => Math.hypot(p.E - q.E, p.N - q.N) < 250;
  if ((near(a, G.start) || G.marks.some(m => near(a, m))) && near(b, G.target)) { G.done.az = true; updateChecklist(); }
}

/* ---------- קלט עכבר / מגע במפה ---------- */
(() => {
  const ptrs = new Map(); let moved = 0, last = null, pinch = null, rulerDrag = false, second = false;
  mapCv.addEventListener('pointerdown', e => {
    mapCv.setPointerCapture(e.pointerId); ptrs.set(e.pointerId, { x: e.offsetX, y: e.offsetY });
    moved = 0; last = { x: e.offsetX, y: e.offsetY };
    if (ptrs.size === 2) { const [p, q] = [...ptrs.values()]; pinch = { d: Math.hypot(p.x - q.x, p.y - q.y), z: MV.z }; rulerDrag = false; return; }
    // מד־זווית: לחיצה וגרירה מנקודה לנקודה (או שתי לחיצות)
    rulerDrag = G.tool === 'ruler' && !!G.lv.ruler && G.phase !== 'final' && G.phase !== 'done' && !!T;
    if (rulerDrag) {
      second = G.ruler.length === 1;
      if (!second) G.ruler = [snapPt(s2w(e.offsetX, e.offsetY))];
      updateRuler(); drawMap();
    }
  });
  mapCv.addEventListener('pointermove', e => {
    if (G.lv.cursorNZ && T && G.phase !== 'idle') { const p = s2w(e.offsetX, e.offsetY); $('cursorOut').textContent = inside(p.E, p.N) ? `סמן: נ״צ ${fmtNZ(p.E, p.N)}` : ''; }
    if (!ptrs.has(e.pointerId)) return;
    ptrs.set(e.pointerId, { x: e.offsetX, y: e.offsetY });
    if (ptrs.size === 2 && pinch) {
      const [p, q] = [...ptrs.values()];
      MV.z = pinch.z * Math.hypot(p.x - q.x, p.y - q.y) / (pinch.d || 1); clampView(); moved = 99; drawMap(); return;
    }
    const dx = e.offsetX - last.x, dy = e.offsetY - last.y; moved += Math.abs(dx) + Math.abs(dy); last = { x: e.offsetX, y: e.offsetY };
    if (rulerDrag) {
      if (moved > 6) { G.ruler = [G.ruler[0], s2w(e.offsetX, e.offsetY)]; updateRuler(); drawMap(); }
      return;
    }
    if (moved > 6) {
      const r = rad(-MV.rot), ux = dx * Math.cos(r) - dy * Math.sin(r), uy = dx * Math.sin(r) + dy * Math.cos(r);
      MV.cx -= ux / MV.z; MV.cy += uy / MV.z; clampView(); drawMap();
    }
  });
  const up = e => {
    if (!ptrs.has(e.pointerId)) return;
    ptrs.delete(e.pointerId);
    if (ptrs.size < 2) pinch = null;
    if (rulerDrag) {
      rulerDrag = false;
      if (moved > 6 || second) G.ruler = [G.ruler[0], snapPt(s2w(e.offsetX, e.offsetY))];
      updateRuler(); drawMap(); return;
    }
    if (moved <= 6 && ptrs.size === 0 && e.type === 'pointerup') onMapTap(e.offsetX, e.offsetY);
  };
  mapCv.addEventListener('pointerup', up); mapCv.addEventListener('pointercancel', up);
  mapCv.addEventListener('wheel', e => {
    e.preventDefault(); if (!T) return;
    const before = s2w(e.offsetX, e.offsetY);
    MV.z *= e.deltaY < 0 ? 1.18 : 1 / 1.18; clampView();
    const after = s2w(e.offsetX, e.offsetY); MV.cx += before.E - after.E; MV.cy += before.N - after.N; clampView(); drawMap();
  }, { passive: false });
})();

/* =======================================================================
   8. סיום ותוצאות
   ======================================================================= */
function finish() {
  stopWalk();
  G.phase = 'done'; G.done.final = true; updateChecklist();
  setControlsEnabled(false);
  mapMsg('');
  const dTarget = Math.hypot(G.pos.E - G.target.E, G.pos.N - G.target.N);
  const dGuess = Math.hypot(G.guess.E - G.pos.E, G.guess.N - G.pos.N);
  const guessToTarget = Math.hypot(G.guess.E - G.target.E, G.guess.N - G.target.N);
  const mine = evalPath(G.path.concat([G.pos]));
  const ideal = G.ideal ? evalPath(G.ideal) : null;
  const straight = evalPath([G.start, G.target]);
  const eff = ideal && mine.time > 0 ? clamp(ideal.time / mine.time, 0, 1) : 0;
  // כמה מהדרך שלי עברה בקרבת הציר האידיאלי (עד 120 מ׳)
  let nearIdeal = 0;
  if (G.ideal && G.path.length > 1) {
    const segD = (p, a, b) => { const vx = b.E - a.E, vy = b.N - a.N, l2 = vx * vx + vy * vy || 1, t = clamp(((p.E - a.E) * vx + (p.N - a.N) * vy) / l2, 0, 1); return Math.hypot(p.E - a.E - t * vx, p.N - a.N - t * vy); };
    let c = 0;
    for (const p of G.path) { let m = Infinity; for (let k = 1; k < G.ideal.length; k++) m = Math.min(m, segD(p, G.ideal[k - 1], G.ideal[k])); if (m <= 120) c++; }
    nearIdeal = c / G.path.length;
  }
  const marks = G.marks.filter(m => m.truth).map(m => Math.hypot(m.E - m.truth.E, m.N - m.truth.N));

  // ניקוד
  const sArrive = 40 * clamp(1 - (dTarget - 30) / 470, 0, 1);
  const sSelf = 25 * clamp(1 - (dGuess - 25) / 275, 0, 1);
  const sEff = 25 * clamp((eff - 0.4) / 0.55, 0, 1);
  const sDot = G.lv.targetShown ? 10 : 10 * clamp(1 - ((G.dotErr ?? 999) - 40) / 260, 0, 1);
  const score = Math.round(clamp(sArrive + sSelf + sEff + sDot - 5 * G.gps, 0, 100));
  const grade = score >= 90 ? 'מנווט מצטיין 🏅' : score >= 75 ? 'ניווט טוב מאוד' : score >= 60 ? 'עבר — יש מה לשפר' : 'לא עבר — שווה ניסיון נוסף';
  const verdict = dTarget <= 50 ? '🎯 פגיעה ביעד!' : dTarget <= 150 ? '✓ הגעתם לאזור היעד' : dTarget <= 400 ? '⚠️ פספוס בינוני' : '✗ פספוס משמעותי';

  // טיפים
  const tips = [];
  if (dTarget > 150 && dGuess <= 120) tips.push('ידעתם היטב איפה אתם, אבל עצרתם רחוק מהיעד. בפעם הבאה, כשמזהים שלא הגעתם, ממשיכים עד שהתוואי של היעד (גבעה, ערוץ, מפגש ערוצים) תואם את המפה.');
  if (dGuess > 200) tips.push('המיקום שדקרתם רחוק מהמיקום האמיתי. כדאי לעצור בנקודות ביניים: לזהות תוואים בולטים, לקחת אזימוט לפסגה ולהשוות את מניין הצעדים למרחק במפה.');
  if (dTarget > 150 && dGuess > 200) tips.push('כדאי לבחור קו מוביל או קו עצירה (ערוץ, רכס) שיעצור אתכם ליד היעד גם אם הסטיתם מהאזימוט.');
  if (ideal && eff < 0.7) tips.push(`הדרך שלכם הייתה איטית ב־${Math.round((1 / Math.max(eff, 0.01) - 1) * 100)}% מהציר האידיאלי. הירוק הוא הציר שחוסך עליות וירידות מיותרות. תכננו לפי קווי הגובה ולא רק בקו ישר.`);
  if (straight.blocked) tips.push('הקו הישר בין המוצא ליעד חוצה מדרון בלתי עביר. במקרה כזה בונים ציר עם נקודת ביניים ועוקפים את המכשול.');
  if (!G.everOriented) tips.push('לא הצפנתם את המפה אף פעם. מפה מוצפנת מקלה מאוד על הצלבה בין השטח למפה.');
  if (G.gps) tips.push(`השתמשתם ב־${G.gps} בדיקות GPS (−${5 * G.gps} נק׳). בשטח אין GPS, לכן כדאי לתרגל זיהוי עצמי של המיקום.`);
  if (!tips.length) tips.push('ניווט נקי: זיהוי נכון של המיקום, הגעה ליעד ודרך יעילה. נסו רמה קשה יותר או גזרה אחרת.');

  // שיא אישי
  let best = null;
  try { const key = `nav-best-${T.meta.id}-${G.level}`; best = +localStorage.getItem(key) || null; if (!best || score > best) localStorage.setItem(key, score); } catch (e) {}

  const R = (lbl, val) => `<div class="result"><div class="val">${val}</div><div class="lbl">${lbl}</div></div>`;
  $('results').innerHTML = `
    <h3>${verdict}</h3>
    <div class="g-score"><span class="big">${score}</span><div><b>${grade}</b><div class="small">מתוך 100 · ${G.lv.name} · ${T.meta.name}${best ? ` · השיא הקודם שלכם: ${best}` : ''}</div></div></div>
    <div class="g-res-grid">
      ${R('המרחק שלכם מהיעד', fmtDist(dTarget))}
      ${R('דיוק דקירת המיקום שלכם', fmtDist(dGuess))}
      ${R('הדקירה שלכם ← היעד', fmtDist(guessToTarget))}
      ${R('יעילות הדרך (זמן אידיאלי / שלכם)', Math.round(eff * 100) + '%')}
      ${R('מהדרך שלכם על הציר האידיאלי', Math.round(nearIdeal * 100) + '%')}
      ${R('הדרך שלכם: מרחק · זמן', `${fmtDist(mine.dist)} · ${fmtTime(mine.time)}`)}
      ${ideal ? R('הציר האידיאלי: מרחק · זמן', `${fmtDist(ideal.dist)} · ${fmtTime(ideal.time)}`) : ''}
      ${R('קו ישר (אווירי)', fmtDist(straight.dist) + (straight.blocked ? ' ⛔ חוצה מצוק' : ''))}
      ${R('טיפוס מצטבר: שלכם · אידיאלי', `${Math.round(mine.climb)} · ${ideal ? Math.round(ideal.climb) : '—'} מ׳`)}
      ${R('צמדי צעדים · צעדים ל־100 מ׳', `${G.paces.toLocaleString('he-IL')} · ${G.walked ? Math.round(G.paces / G.walked * 100) : '—'}`)}
      ${!G.lv.targetShown ? R('דקירת היעד (ניסיון ראשון)', G.dotErr === null ? '—' : fmtDist(G.dotErr)) : ''}
      ${marks.length ? R('דיוק סימוני ✏️ בדרך (ממוצע)', fmtDist(marks.reduce((a, b) => a + b, 0) / marks.length)) : ''}
    </div>
    <div class="g-res-legend">
      <span><i style="border-top:3px solid #d0342c"></i>הדרך שלכם</span>
      <span><i style="border-top:3px dashed #1f8a3a"></i>ציר אידיאלי (מהיר ביותר לפי התבליט)</span>
      <span><i style="border-top:2px dotted #555"></i>קו ישר</span>
      <span>🟠 המיקום האמיתי · ⊕ הדקירה שלכם · ◎ היעד</span>
    </div>
    <h4 style="margin:6px 0 0">מה לקחת מהניווט הזה</h4>
    <ul class="g-tips">${tips.map(t => `<li>${t}</li>`).join('')}</ul>
    <p class="small">ניקוד: הגעה ליעד 40 · דיוק דקירה עצמית 25 · יעילות הדרך 25 · דקירת היעד 10 · כל בדיקת GPS מורידה 5 נקודות.</p>
    <div class="g-res-actions">
      <button class="btn" id="againBtn">🔁 ניווט חדש באותה גזרה</button>
      <button class="btn ghost-dark" id="setupBtn">🗺️ גזרה או רמה אחרת</button>
    </div>`;
  $('results').classList.remove('hidden');
  $('againBtn').addEventListener('click', () => { newMission(); window.scrollTo({ top: 0, behavior: 'smooth' }); });
  $('setupBtn').addEventListener('click', showSetup);
  // מסגור המפה כך שכל המסלולים ייראו
  const all = [G.start, G.target, G.pos, G.guess, ...G.path, ...(G.ideal || [])];
  const Es = all.map(p => p.E), Ns = all.map(p => p.N);
  MV.rot = 0; $('orientLock').checked = false;
  const span = Math.max(Math.max(...Es) - Math.min(...Es), Math.max(...Ns) - Math.min(...Ns)) * 1.25 + 300;
  fitMap({ E: (Math.max(...Es) + Math.min(...Es)) / 2, N: (Math.max(...Ns) + Math.min(...Ns)) / 2 }, span / 1000);
  drawMap();
  $('results').scrollIntoView({ behavior: 'smooth', block: 'start' });
}

function setControlsEnabled(on) {
  document.querySelectorAll('.g-ctrl button, .g-ctrl input').forEach(b => { b.disabled = !on; });
  $('arriveBtn').textContent = '🏁 הגעתי — דקירת מיקום';
}

function updateChecklist() {
  document.querySelectorAll('#checklist li').forEach(li => li.classList.toggle('done', !!G.done[li.dataset.k]));
}

/* =======================================================================
   9. מסך פתיחה, אירועים והפעלה
   ======================================================================= */
function showSetup() {
  stopWalk(); G.phase = 'idle';
  $('gameScreen').classList.add('hidden'); $('setupScreen').classList.remove('hidden');
  window.scrollTo({ top: 0 });
}

async function startGame() {
  const btn = $('startBtn');
  btn.disabled = true; btn.textContent = '⏳ טוען שטח ובונה מפה…';
  G.level = document.querySelector('input[name="lvl"]:checked').value; G.lv = LEVELS[G.level];
  try {
    if (!T || T.meta.id !== G.region.id) { await loadTerrain(G.region); await new Promise(r => setTimeout(r, 20)); buildMapBase(); }
    $('setupScreen').classList.add('hidden'); $('gameScreen').classList.remove('hidden');
    await new Promise(r => requestAnimationFrame(r));
    newMission();
  } catch (e) {
    console.error(e);
    alert('טעינת השטח נכשלה. אם פתחתם את הקובץ ישירות מהמחשב, הריצו שרת מקומי (python3 -m http.server).');
  }
  btn.disabled = false; btn.textContent = '🧭 צאו לניווט';
}

function bindUI() {
  document.querySelectorAll('[data-turn]').forEach(b => b.addEventListener('click', () => turn(+b.dataset.turn)));
  document.querySelectorAll('[data-walk]').forEach(b => b.addEventListener('click', () => startWalk(+b.dataset.walk)));
  const hold = $('holdWalk');
  hold.addEventListener('pointerdown', e => { e.preventDefault(); startWalk(0); });
  ['pointerup', 'pointerleave', 'pointercancel'].forEach(ev => hold.addEventListener(ev, () => { if (walking && walking.hold) stopWalk(); }));
  const setAz = () => {
    const v = parseFloat($('azIn').value);
    if (!isFinite(v)) return;
    G.hd = norm360(v + DECL);   // מגנטי ← רשת
    updateHUD(); renderView(); if (lockOrient()) drawMap(); else updateOrient();
    fieldMsg(`🧭 המצפן מכוון לאזימוט מגנטי ${Math.round(norm360(v))}°.`, '');
    if (!G.lv.ruler) { const want = azimuth(G.target.E - G.start.E, G.target.N - G.start.N) - DECL; if (Math.abs(angDiff(v, want)) < 6) { G.done.az = true; updateChecklist(); } }
  };
  $('azSet').addEventListener('click', setAz);
  $('azIn').addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); setAz(); } });
  $('paceReset').addEventListener('click', () => { G.legPaces = 0; updateHUD(); });
  $('gpsBtn').addEventListener('click', () => {
    if (G.phase !== 'nav' && G.phase !== 'dot') return;
    G.gps++; G.gpsUntil = performance.now() + 4000; updateHUD(); drawMap();
    fieldMsg('🛰️ המיקום האמיתי מוצג במפה ל־4 שניות (−5 נקודות).', 'bad');
    setTimeout(drawMap, 4050);
  });
  $('arriveBtn').addEventListener('click', () => {
    if (G.phase === 'final') {
      if (!G.guess) { mapMsg('🏁 לחצו על המפה במקום שבו אתם חושבים שאתם נמצאים.'); return; }
      finish(); return;
    }
    if (G.phase !== 'nav') { if (G.phase === 'dot') mapMsg('📍 קודם דקרו את נקודת היעד על המפה.'); return; }
    stopWalk(); G.phase = 'final'; setTool('pan'); mapCv.classList.add('crosshair');
    mapMsg('🏁 לחצו על המפה במקום שבו אתם חושבים שאתם נמצאים עכשיו.');
    $('arriveBtn').textContent = '✅ אשר דקירה וסיים';
    $('mapWrap').scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  });
  document.querySelectorAll('#mapTools .tool').forEach(b => b.addEventListener('click', () => {
    if (G.phase === 'final' || G.phase === 'done') return;
    if (b.dataset.tool === 'dot' && G.phase !== 'dot') return;
    setTool(b.dataset.tool);
    if (b.dataset.tool === 'ruler') $('rulerOut').textContent = '📐 לחצו על נקודת מוצא ואחר כך על נקודת יעד';
  }));
  $('clearMarks').addEventListener('click', () => {
    if (G.phase === 'done') return;
    G.marks = []; G.ruler = []; G.backLines = []; G.bearings = []; G.pendingBearing = null;
    $('rulerOut').textContent = ''; $('backBtn').classList.add('hidden'); drawMap(); drawView();
  });
  $('backBtn').addEventListener('click', () => {
    if (!G.pendingBearing || G.phase === 'final' || G.phase === 'done') return;
    setTool('back');
    mapMsg(`🎯 לחצו על המפה על התוואי שאליו לקחתם את אזימוט ${G.pendingBearing.n} (למשל ▲ נקודת גובה). ישורטט ממנו הקו החוזר.`);
    $('mapWrap').scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  });
  $('optContours').addEventListener('change', e => { VIEWOPT.contours = e.target.checked; if (T && G.phase !== 'idle') renderView(); });
  $('optPeaks').addEventListener('change', e => { VIEWOPT.peaks = e.target.checked; if (T && G.phase !== 'idle') renderView(); });
  $('strongShade').addEventListener('change', e => { MAPOPT.strong = e.target.checked; if (T) { buildMapBase(); drawMap(); } });
  $('zoomIn').addEventListener('click', () => { MV.z *= 1.4; clampView(); drawMap(); });
  $('zoomOut').addEventListener('click', () => { MV.z /= 1.4; clampView(); drawMap(); });
  $('rotL').addEventListener('click', () => rotateMap(-15));
  $('rotR').addEventListener('click', () => rotateMap(15));
  $('rotReset').addEventListener('click', () => { $('orientLock').checked = false; MV.rot = 0; drawMap(); });
  $('centerStart').addEventListener('click', () => { MV.cx = G.start.E; MV.cy = G.start.N; clampView(); drawMap(); });
  $('orientLock').addEventListener('change', () => { if (lockOrient()) drawMap(); });
  $('startBtn').addEventListener('click', startGame);
  $('navSetup').addEventListener('click', e => { e.preventDefault(); showSetup(); });

  // מקלדת
  const keys = new Set();
  document.addEventListener('keydown', e => {
    if (e.target.tagName === 'INPUT' || G.phase === 'idle' || G.phase === 'done') return;
    if (e.key === 'ArrowLeft' || e.key === 'ArrowRight') { e.preventDefault(); turn((e.key === 'ArrowLeft' ? -1 : 1) * (e.shiftKey ? 10 : 2)); }
    else if ((e.key === 'ArrowUp' || e.key === 'w' || e.key === 'W' || e.key === "'") && !keys.has('up')) { e.preventDefault(); keys.add('up'); startWalk(0); }
    else if (e.key === 'g' || e.key === 'G' || e.key === 'ע') { MV.cx = G.start.E; MV.cy = G.start.N; clampView(); drawMap(); }
  });
  document.addEventListener('keyup', e => {
    if (e.key === 'ArrowUp' || e.key === 'w' || e.key === 'W' || e.key === "'") { keys.delete('up'); if (walking && walking.hold) stopWalk(); }
  });
  window.addEventListener('blur', () => { keys.clear(); if (walking && walking.hold) stopWalk(); });
  let rt = null;
  window.addEventListener('resize', () => { clearTimeout(rt); rt = setTimeout(() => { if (T && G.phase !== 'idle') { drawView(); drawMap(); } }, 120); });

  // ערכת נושא
  const tbtn = $('themeToggle');
  const sync = () => { tbtn.textContent = document.documentElement.getAttribute('data-theme') === 'dark' ? '☀️' : '🌙'; };
  sync();
  tbtn.addEventListener('click', () => {
    const next = document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', next);
    try { localStorage.setItem('theme', next); } catch (e) {}
    sync();
  });
}

const REGION_NOTE = {
  tabor: 'הר בודד מעל עמק — קל לזהות',
  meron: 'גליל הררי ומיוער, ערוצים עמוקים',
  carmel: 'רכס, ואדיות וחורש ים־תיכוני',
  gush: 'שלוחות וגבעות בהרי יהודה',
  judea: 'מצוקים וערוצים יבשים — אתגר',
  ramon: 'מצוק המכתש ורמות מדבריות',
};

(async function init() {
  bindUI();
  try { await loadRegions(); } catch (e) {
    $('regionList').innerHTML = '<p class="feedback bad">טעינת הגזרות נכשלה. אם פתחתם את הקובץ ישירות מהמחשב, הריצו שרת מקומי (python3 -m http.server).</p>';
    return;
  }
  const list = $('regionList'); list.innerHTML = '';
  REGIONS.forEach((r, k) => {
    const b = document.createElement('button');
    b.className = 'g-region'; b.type = 'button';
    b.innerHTML = `<b>${r.name}</b><span>${REGION_NOTE[r.id] || ''} · גבהים ${r.hmin}–${r.hmax} מ׳</span>`;
    b.addEventListener('click', () => {
      G.region = r; list.querySelectorAll('.g-region').forEach(x => x.classList.toggle('on', x === b));
      $('startBtn').disabled = false; showBest();
    });
    list.appendChild(b);
    if (k === 0) b.click();
  });
  document.querySelectorAll('input[name="lvl"]').forEach(i => i.addEventListener('change', showBest));
})();

function showBest() {
  const lvl = document.querySelector('input[name="lvl"]:checked').value;
  let b = null; try { b = localStorage.getItem(`nav-best-${G.region.id}-${lvl}`); } catch (e) {}
  $('bestLine').textContent = b ? `🏅 השיא שלכם בגזרה וברמה האלה: ${b}` : '';
}
