#!/usr/bin/env python3
# בונה לכל גזרה במשחק הניווט:
#   <id>_sat.jpg — תצלום לוויין Sentinel-2 בצבע אמיתי (5 מ׳ לפיקסל, רשת ישראל החדשה), פסיפס בלי עננים
#   <id>_lc.png  — כיסוי קרקע ESA WorldCover 2021 (10 מ׳ לפיקסל; ערך = קוד המחלקה)
# שימוש: python3 tools/build_game_imagery.py assets/game [מזהי גזרות...]
# דורש: rasterio, numpy, pillow, pyproj, mgrs. מקורות: AWS Open Data (sentinel-cogs, esa-worldcover)
import os, sys, json, re, urllib.request
import numpy as np, rasterio, mgrs
from rasterio.warp import reproject, Resampling
from rasterio.transform import from_origin
from PIL import Image
from pyproj import Transformer

OUT = sys.argv[1]
os.environ.setdefault('GDAL_DISABLE_READDIR_ON_OPEN', 'EMPTY_DIR')
S2 = 'https://sentinel-cogs.s3.us-west-2.amazonaws.com/'
WC = 'https://esa-worldcover.s3.eu-central-1.amazonaws.com/v200/2021/map/ESA_WorldCover_10m_2021_v200_{}_Map.tif'
MONTHS = [(2024, 4), (2023, 4), (2024, 5), (2023, 5), (2024, 3), (2023, 3), (2024, 6)]
SIZE, SAT_RES, LC_RES = 8000, 5.0, 10.0
to_wgs = Transformer.from_crs(2039, 4326, always_xy=True)
M = mgrs.MGRS()

def scenes(tile, y, m):
  z, band, sq = tile[:2], tile[2], tile[3:]
  pre = f'sentinel-s2-l2a-cogs/{int(z)}/{band}/{sq}/{y}/{m}/'
  x = urllib.request.urlopen(f'{S2}?list-type=2&prefix={pre}&delimiter=/', timeout=60).read().decode()
  out = []
  for p in re.findall(r'<Prefix>([^<]+)</Prefix>', x)[1:]:
    name = p.rstrip('/').split('/')[-1]
    try:
      j = json.load(urllib.request.urlopen(f'{S2}{p}{name}.json', timeout=60))
      out.append((j['properties'].get('eo:cloud_cover', 100), j['properties'].get('s2:nodata_pixel_percentage', 100), S2 + p))
    except Exception as e:
      print('  skip', name, e)
  return out

def warp(url, dst_shape, dst_tf, resampling, bands, dtype):
  with rasterio.open('/vsicurl/' + url) as ds:
    dst = np.zeros((len(bands),) + dst_shape, dtype)
    for k, b in enumerate(bands):
      reproject(rasterio.band(ds, b), dst[k], dst_transform=dst_tf, dst_crs='EPSG:2039', resampling=resampling, src_nodata=0, dst_nodata=0)
    return dst

def save_sat(img, path):
  # החזרה ← צבע: נקודת לבן לפי הגזרה (בהירה במדבר; גגות בודדים לא קובעים), וגמא שמבהירה צמחייה כהה
  wp = float(np.clip(np.percentile(img.mean(axis=0), 98) * 1.1, 0.17, 0.62))
  f = np.clip(img / wp, 0, 1) ** (1 / 1.6)
  print(f'  white point {wp:.3f}', flush=True)
  Image.fromarray((f * 255).astype(np.uint8).transpose(1, 2, 0)).save(path, quality=84, optimize=True, progressive=True)

regions = json.load(open(os.path.join(OUT, 'regions.json')))
if len(sys.argv) > 2: regions = [r for r in regions if r['id'] in sys.argv[2:]]
for r in regions:
  e0, n0 = r['e0'], r['n0']
  print(r['id'], flush=True)
  # --- Sentinel-2 ---
  n = int(SIZE / SAT_RES); tf = from_origin(e0, n0 + SIZE, SAT_RES, SAT_RES)
  tiles = set()
  for fx in (0, 0.5, 1):
    for fy in (0, 0.5, 1):
      lon, lat = to_wgs.transform(e0 + fx * SIZE, n0 + fy * SIZE)
      t = M.toMGRS(lat, lon, MGRSPrecision=0)
      tiles.add(t)
      # ליד גבול רצועות הרוחב Sentinel-2 מסווג לפעמים את המשבצת באות הרצועה השכנה
      tiles.add(t[:2] + {'R': 'S', 'S': 'R'}.get(t[2], t[2]) + t[3:])
  cands = []
  for (y, m) in MONTHS:
    for t in tiles:
      cands += [c for c in scenes(t, y, m) if c[0] < 20]
    if sum(1 for c in cands if c[0] < 3) >= 3 * len(tiles): break
  cands.sort()
  img = np.zeros((3, n, n), np.float32); filled = np.zeros((n, n), bool)
  for cc, nd, url in cands:
    # ערוצי החזרה גולמיים (B04/B03/B02): ה־TCI המוכן "נשרף" בלבן מעל מדבר
    rgb = np.concatenate([warp(url + b, (n, n), tf, Resampling.bilinear, (1,), np.uint16) for b in ('B04.tif', 'B03.tif', 'B02.tif')])
    scl = warp(url + 'SCL.tif', (n, n), tf, Resampling.nearest, (1,), np.uint8)[0]
    good = (rgb.min(axis=0) > 0) & ~np.isin(scl, (0, 1, 3, 8, 9, 10)) & ~filled
    img[:, good] = np.clip(rgb[:, good] * 0.0001, 0, 1); filled |= good   # ב־sentinel-cogs ההיסט (BOA offset) כבר הוחל
    print(f'  {url.split("/")[-2]} cloud {cc:.1f}% -> filled {filled.mean() * 100:.1f}%', flush=True)
    if filled.mean() > 0.999: break
  # השלמת חורים קטנים בממוצע שכנים
  for _ in range(20):
    if filled.all(): break
    pad = np.pad(img, ((0, 0), (1, 1), (1, 1)), mode='edge'); pf = np.pad(filled, 1, mode='edge').astype(np.float32)
    s = sum(pad[:, 1 + dy:1 + dy + n, 1 + dx:1 + dx + n] * pf[1 + dy:1 + dy + n, 1 + dx:1 + dx + n] for dy in (-1, 0, 1) for dx in (-1, 0, 1))
    c = sum(pf[1 + dy:1 + dy + n, 1 + dx:1 + dx + n] for dy in (-1, 0, 1) for dx in (-1, 0, 1))
    new = ~filled & (c > 0)
    img[:, new] = s[:, new] / c[new]; filled |= new
  cache = os.environ.get('S2_CACHE')
  if cache: np.save(os.path.join(cache, r['id'] + '.npy'), img)
  save_sat(img, os.path.join(OUT, f"{r['id']}_sat.jpg"))

  # --- WorldCover ---
  n2 = int(SIZE / LC_RES); tf2 = from_origin(e0, n0 + SIZE, LC_RES, LC_RES)
  lc = np.zeros((n2, n2), np.uint8)
  names = set()
  for fx in (0, 1):
    for fy in (0, 1):
      lon, lat = to_wgs.transform(e0 + fx * SIZE, n0 + fy * SIZE)
      names.add(f'N{int(lat // 3 * 3):02d}E{int(lon // 3 * 3):03d}')
  for nm in sorted(names):
    part = warp(WC.format(nm), (n2, n2), tf2, Resampling.mode, (1,), np.uint8)[0]
    lc = np.where(lc == 0, part, lc)
  Image.fromarray(lc, mode='L').save(os.path.join(OUT, f"{r['id']}_lc.png"), optimize=True)
  u, c = np.unique(lc, return_counts=True)
  print('  landcover', dict(zip(u.tolist(), (c / c.sum()).round(3).tolist())), flush=True)
