// ENDLESS PUZZLE：ネットが無くても開けるようにする仕組み（サービスワーカー）
// - 最初に本体（ページ・問題を作る gen.js・アイコン類）を全部控える
// - 同じサイトのファイル：ネットがあれば最新を取りに行き、無い・遅いときは控えを出す
// - 字（Google Fonts）：一度読めたものは控えておく
// 記録（localStorage）には触らない。
const CACHE = 'endless-puzzle-v2';
const PRECACHE = ['./', './gen.js', './manifest.webmanifest', './icon-192.png', './icon-512.png', './apple-touch-icon.png', './favicon-32.png', './icon-maskable-512.png'];
const WAIT_MS = 3000;

self.addEventListener('install', (e) => {
  e.waitUntil(
    caches.open(CACHE)
      .then((c) => Promise.all(PRECACHE.map((p) => c.add(new Request(p, { cache: 'reload' })).catch(() => null))))
      .then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', (e) => {
  e.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

function keyOf(url) {
  // ?v=2 などは外して控える。ページは './' にそろえる
  const u = new URL(url); u.search = '';
  if (u.pathname.endsWith('/index.html')) u.pathname = u.pathname.slice(0, -10);
  return u.toString();
}

function fromNetwork(req, key) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error('timeout')), WAIT_MS);
    fetch(req, { cache: 'no-cache' }).then((res) => {
      clearTimeout(timer);
      if (res.ok) { const copy = res.clone(); caches.open(CACHE).then((c) => c.put(key, copy)); }
      resolve(res);
    }, (err) => { clearTimeout(timer); reject(err); });
  });
}

self.addEventListener('fetch', (e) => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);

  if (url.origin === location.origin) {
    const key = keyOf(req.url);
    e.respondWith(
      fromNetwork(req, key).catch(() =>
        caches.match(key).then((hit) => hit || (req.mode === 'navigate'
          ? new Response('<meta charset="utf-8"><p style="font:16px sans-serif;padding:24px">一度ネットにつないで開いてください。</p>',
              { headers: { 'Content-Type': 'text/html; charset=utf-8' } })
          : Response.error()))
      )
    );
    return;
  }

  if (url.hostname === 'fonts.googleapis.com' || url.hostname === 'fonts.gstatic.com') {
    e.respondWith(
      caches.open(CACHE).then((c) =>
        c.match(req).then((hit) => hit || fetch(req).then((res) => {
          if (res.ok || res.type === 'opaque') c.put(req, res.clone());
          return res;
        }))
      )
    );
  }
});
