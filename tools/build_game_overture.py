#!/usr/bin/env python3
# מחלץ מ־Overture Maps (נגזר מ־OpenStreetMap ועוד) כבישים, דרכי עפר, שבילים ושמות יישובים לכל גזרה.
# פלט: assets/game/<id>_ov.json — קואורדינטות במטרים יחסית לפינה הדרום־מערבית של הגזרה (רשת ישראל החדשה)
# שימוש: python3 tools/build_game_overture.py assets/game [release]
# דורש: pyarrow, shapely, pyproj. נתונים: Overture Maps Foundation (ODbL / CDLA), AWS Open Data
import os, sys, re, json, urllib.request
import pyarrow.parquet as pq
from shapely import wkb
from shapely.geometry import box
from shapely.ops import transform as shp_transform
from pyproj import Transformer
sys.path.insert(0, os.path.dirname(__file__))
from overture_range import RangeFile

OUT = sys.argv[1]
B = 'https://overturemaps-us-west-2.s3.us-west-2.amazonaws.com/'
SIZE = 8000
to_wgs = Transformer.from_crs(2039, 4326, always_xy=True)
to_itm = Transformer.from_crs(4326, 2039, always_xy=True)

def latest_release():
  x = urllib.request.urlopen(B + '?list-type=2&prefix=release/&delimiter=/').read().decode()
  return re.findall(r'<Prefix>(release/[^<]+)</Prefix>', x)[-1]

def files(prefix):
  x = urllib.request.urlopen(B + f'?list-type=2&prefix={prefix}').read().decode()
  return list(zip(re.findall(r'<Key>([^<]+)</Key>', x), map(int, re.findall(r'<Size>(\d+)</Size>', x))))

def read_bbox(prefix, bb, columns):
  # קורא רק את קבוצות השורות שה־bbox שלהן חותך את האזור
  out = []
  for key, size in files(prefix):
    f = pq.ParquetFile(RangeFile(B + key, size))
    md = f.metadata
    idx = {md.row_group(0).column(c).path_in_schema: c for c in range(md.row_group(0).num_columns)}
    hits = []
    for g in range(md.num_row_groups):
      rg = md.row_group(g)
      st = lambda n: rg.column(idx[n]).statistics
      if st('bbox.xmax').max < bb[0] or st('bbox.xmin').min > bb[2] or st('bbox.ymax').max < bb[1] or st('bbox.ymin').min > bb[3]: continue
      hits.append(g)
    if hits:
      t = f.read_row_groups(hits, columns=columns)
      out.append(t)
      print(f'  {key.split("/")[-1][:12]} groups {hits} rows {t.num_rows}', flush=True)
  return out

def he_name(names):
  if not names: return None
  common = dict(names.get('common') or [])
  return common.get('he') or names.get('primary')

regions = json.load(open(os.path.join(OUT, 'regions.json')))
boxes = {}
for r in regions:
  pts = [to_wgs.transform(r['e0'] + dx, r['n0'] + dy) for dx in (0, SIZE) for dy in (0, SIZE)]
  boxes[r['id']] = (min(p[0] for p in pts), min(p[1] for p in pts), max(p[0] for p in pts), max(p[1] for p in pts))
allbb = (min(b[0] for b in boxes.values()), min(b[1] for b in boxes.values()), max(b[2] for b in boxes.values()), max(b[3] for b in boxes.values()))
rel = sys.argv[2] if len(sys.argv) > 2 else latest_release()
print('release', rel, 'bbox', allbb)

# --- כבישים ושבילים ---
seg_tables = read_bbox(f'{rel}theme=transportation/type=segment/', allbb, ['names', 'subtype', 'class', 'geometry', 'bbox'])
# --- יישובים ---
div_tables = read_bbox(f'{rel}theme=divisions/type=division/', allbb, ['names', 'subtype', 'class', 'geometry', 'bbox', 'population'])

KEEP = {'motorway': 'M', 'trunk': 'M', 'primary': 'P', 'secondary': 'S', 'tertiary': 'S', 'unclassified': 'R', 'residential': 'R',
        'living_street': 'R', 'service': 'V', 'track': 'T', 'path': 'F', 'footway': 'F', 'bridleway': 'F', 'cycleway': 'F', 'steps': 'F'}
for r in regions:
  bb = boxes[r['id']]
  clip = box(r['e0'], r['n0'], r['e0'] + SIZE, r['n0'] + SIZE)
  roads, places = [], []
  for t in seg_tables:
    for row in t.to_pylist():
      b = row['bbox']
      if b['xmax'] < bb[0] or b['xmin'] > bb[2] or b['ymax'] < bb[1] or b['ymin'] > bb[3]: continue
      if row['subtype'] != 'road' and row['subtype'] != 'rail': continue
      cls = 'X' if row['subtype'] == 'rail' else KEEP.get(row['class'])
      if not cls: continue
      g = shp_transform(lambda x, y, z=None: to_itm.transform(x, y), wkb.loads(row['geometry'])).intersection(clip)
      if g.is_empty: continue
      lines = [g] if g.geom_type == 'LineString' else [q for q in getattr(g, 'geoms', []) if q.geom_type == 'LineString']
      for ln in lines:
        ln = ln.simplify(2.0)
        pts = [v for x, y in ln.coords for v in (round(x - r['e0']), round(y - r['n0']))]
        if len(pts) >= 4: roads.append([cls, he_name(row['names']) or ''] + pts)
  for t in div_tables:
    for row in t.to_pylist():
      if row['subtype'] not in ('locality', 'neighborhood', 'microhood'): continue
      b = row['bbox']
      if b['xmax'] < bb[0] or b['xmin'] > bb[2] or b['ymax'] < bb[1] or b['ymin'] > bb[3]: continue
      g = wkb.loads(row['geometry'])
      if g.geom_type != 'Point': g = g.representative_point()
      E, N = to_itm.transform(g.x, g.y)
      if not (r['e0'] <= E <= r['e0'] + SIZE and r['n0'] <= N <= r['n0'] + SIZE): continue
      nm = he_name(row['names'])
      if nm: places.append([nm, round(E - r['e0']), round(N - r['n0']), row['class'] or row['subtype'], row['population'] or 0])
  json.dump({'roads': roads, 'places': places}, open(os.path.join(OUT, f"{r['id']}_ov.json"), 'w'), ensure_ascii=False, separators=(',', ':'))
  from collections import Counter
  print(r['id'], 'roads', len(roads), dict(Counter(x[0] for x in roads)), 'places', len(places), [p[0] for p in places][:12], flush=True)
