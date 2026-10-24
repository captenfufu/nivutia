# קורא קובצי Parquet מרוחקים בבקשות טווח (HTTP Range), בלי להוריד את כל הקובץ
import io, urllib.request

class RangeFile(io.RawIOBase):
  def __init__(self, url, size):
    self.url, self.size, self.pos, self.cache = url, size, 0, {}
  def readable(self): return True
  def seekable(self): return True
  def tell(self): return self.pos
  def seek(self, off, whence=0):
    self.pos = off if whence == 0 else self.pos + off if whence == 1 else self.size + off
    return self.pos
  def read(self, n=-1):
    if n < 0: n = self.size - self.pos
    n = min(n, self.size - self.pos)
    if n <= 0: return b''
    req = urllib.request.Request(self.url, headers={'Range': f'bytes={self.pos}-{self.pos + n - 1}'})
    for attempt in range(4):
      try:
        data = urllib.request.urlopen(req, timeout=120).read(); break
      except Exception:
        if attempt == 3: raise
    self.pos += len(data)
    return data
  def readinto(self, b):
    d = self.read(len(b)); b[:len(d)] = d; return len(d)
