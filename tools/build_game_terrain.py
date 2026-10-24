#!/usr/bin/env python3
# שימוש: python3 tools/build_game_terrain.py <תיקיית_מטמון_אריחים> assets/game
# דורש: numpy, pillow, pyproj
# בונה נתוני גובה לאזורי משחק הניווט מאריחי Terrarium (AWS Open Data, מבוסס SRTM ועוד)
import math, os, sys, json, heapq, urllib.request, io
import numpy as np
from PIL import Image
from pyproj import Transformer

TILES = sys.argv[1]; OUT = sys.argv[2]
Z = 13; CELL = 25.0; SIZE = 8000.0
to_wgs = Transformer.from_crs(2039, 4326, always_xy=True)
to_itm = Transformer.from_crs(4326, 2039, always_xy=True)

REGIONS = [
  ('tabor',  'הר תבור ועמק יזרעאל', 32.6874, 35.3903, 'north'),
  ('meron',  'הר מירון והגליל העליון', 32.995, 35.405, 'north'),
  ('carmel', 'רכס הכרמל', 32.735, 35.025, 'north'),
  ('gush',   'גוש עציון והרי חברון', 31.650, 35.115, 'center'),
  ('judea',  'מדבר יהודה — מצדה', 31.330, 35.330, 'desert'),
  ('ramon',  'מכתש רמון', 30.605, 34.815, 'desert'),
]

cache = {}
def tile(x, y):
  k = (x, y)
  if k in cache: return cache[k]
  p = os.path.join(TILES, f'{Z}_{x}_{y}.png')
  if not os.path.exists(p):
    url = f'https://s3.amazonaws.com/elevation-tiles-prod/terrarium/{Z}/{x}/{y}.png'
    data = urllib.request.urlopen(url, timeout=60).read()
    open(p, 'wb').write(data)
  a = np.asarray(Image.open(p).convert('RGB')).astype(np.float64)
  h = a[..., 0] * 256 + a[..., 1] + a[..., 2] / 256 - 32768
  cache[k] = h
  return h

def elev(lon, lat):
  n = 2 ** Z
  fx = (lon + 180) / 360 * n * 256
  fy = (1 - math.asinh(math.tan(math.radians(lat))) / math.pi) / 2 * n * 256
  fx -= 0.5; fy -= 0.5
  x0, y0 = math.floor(fx), math.floor(fy); tx, ty = fx - x0, fy - y0
  def px(X, Y):
    return tile(X // 256, Y // 256)[Y % 256, X % 256]
  return (px(x0, y0) * (1 - tx) * (1 - ty) + px(x0 + 1, y0) * tx * (1 - ty)
          + px(x0, y0 + 1) * (1 - tx) * ty + px(x0 + 1, y0 + 1) * tx * ty)

def fill_pits(h):
  ny, nx = h.shape; f = np.full_like(h, np.inf); seen = np.zeros(h.shape, bool); pq = []
  for j in range(ny):
    for i in range(nx):
      if i in (0, nx - 1) or j in (0, ny - 1):
        f[j, i] = h[j, i]; seen[j, i] = True; heapq.heappush(pq, (h[j, i], j, i))
  while pq:
    z, j, i = heapq.heappop(pq)
    for dj in (-1, 0, 1):
      for di in (-1, 0, 1):
        jj, ii = j + dj, i + di
        if 0 <= jj < ny and 0 <= ii < nx and not seen[jj, ii]:
          seen[jj, ii] = True; f[jj, ii] = max(h[jj, ii], z + 1e-3); heapq.heappush(pq, (f[jj, ii], jj, ii))
  return f

def streams(h, thresh_cells):
  f = fill_pits(h); ny, nx = h.shape
  rec = -np.ones((ny, nx, 2), int)
  for j in range(ny):
    for i in range(nx):
      best, bd = None, 0
      for dj in (-1, 0, 1):
        for di in (-1, 0, 1):
          if not dj and not di: continue
          jj, ii = j + dj, i + di
          if 0 <= jj < ny and 0 <= ii < nx:
            d = (f[j, i] - f[jj, ii]) / math.hypot(di, dj)
            if d > bd: bd, best = d, (jj, ii)
      if best: rec[j, i] = best
  order = np.argsort(-f, axis=None); acc = np.ones(ny * nx)
  for idx in order:
    j, i = divmod(int(idx), nx); r = rec[j, i]
    if r[0] >= 0: acc[r[0] * nx + r[1]] += acc[idx]
  acc = acc.reshape(ny, nx)
  # שרשור קווים: מכל תא מעל הסף הולכים במורד עד שמצטרפים לקו קיים
  used = np.zeros((ny, nx), bool); lines = []
  cells = [(acc[j, i], j, i) for j in range(ny) for i in range(nx) if acc[j, i] >= thresh_cells]
  # מתחילים מראשי ערוצים (תאים שאף שכן מעליהם לא עובר את הסף)
  for a, j, i in sorted(cells):
    if used[j, i]: continue
    line = [(i, j)]; used[j, i] = True; cj, ci = j, i
    while True:
      r = rec[cj, ci]
      if r[0] < 0: break
      cj, ci = int(r[0]), int(r[1]); line.append((ci, cj))
      if used[cj, ci]: break
      used[cj, ci] = True
    if len(line) >= 3:
      lines.append([round(float(acc[line[-1][1], line[-1][0]]))] + [c for q in line for c in q])
  return lines

def peaks(h, radius=12, min_prom=25):
  ny, nx = h.shape; out = []
  for j in range(2, ny - 2):
    for i in range(2, nx - 2):
      z = h[j, i]
      j0, j1, i0, i1 = max(0, j - radius), min(ny, j + radius + 1), max(0, i - radius), min(nx, i + radius + 1)
      win = h[j0:j1, i0:i1]
      if z >= win.max() and z - win.min() >= min_prom:
        if all(abs(p[0] - i) > 3 or abs(p[1] - j) > 3 for p in out):
          out.append((i, j, z))
  return out

os.makedirs(OUT, exist_ok=True); meta = []
for rid, name, lat, lon, biome in REGIONS:
  E, N = to_itm.transform(lon, lat)
  e0 = round((E - SIZE / 2) / 1000) * 1000; n0 = round((N - SIZE / 2) / 1000) * 1000
  nx = ny = int(SIZE / CELL) + 1
  h = np.zeros((ny, nx))
  for j in range(ny):
    for i in range(nx):
      lo, la = to_wgs.transform(e0 + i * CELL, n0 + j * CELL)
      h[j, i] = elev(lo, la)
  # תיקון חורים (אם יש) והחלקה קלה של רעש
  h = np.where(h < -1000, np.nan, h); h = np.nan_to_num(h, nan=np.nanmean(h))
  k = np.array([[1, 2, 1], [2, 4, 2], [1, 2, 1]]) / 16.0
  hp = np.pad(h, 1, mode='edge'); hs = sum(k[a, b] * hp[a:a + ny, b:b + nx] for a in range(3) for b in range(3))
  (np.round(hs * 10).astype('<i2')).tofile(os.path.join(OUT, f'{rid}.bin'))
  st = streams(hs, thresh_cells=120)
  pk = peaks(hs)
  meta.append(dict(id=rid, name=name, biome=biome, e0=e0, n0=n0, cell=CELL, nx=nx, ny=ny,
                   hmin=round(float(hs.min())), hmax=round(float(hs.max())),
                   peaks=[[int(i), int(j), round(float(z))] for i, j, z in pk],
                   streams=st))
  print(rid, e0, n0, round(hs.min()), round(hs.max()), 'streams', len(st), 'peaks', len(pk), flush=True)
json.dump(meta, open(os.path.join(OUT, 'regions.json'), 'w'), ensure_ascii=False, separators=(',', ':'))
