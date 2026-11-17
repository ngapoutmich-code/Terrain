/* Mich4Track Terrain : fonctionnement hors ligne. La page, le lecteur de secours et les icônes sont gardés sur le téléphone. */
const CACHE="m4terrain-20261117.1029";
const FICHIERS=["./","./index.html","./zxing.min.js","./manifest.webmanifest","./icon-192.png","./icon-512.png"];
self.addEventListener("install",e=>{e.waitUntil(caches.open(CACHE).then(c=>Promise.all(FICHIERS.map(f=>c.add(f).catch(()=>{})))).then(()=>self.skipWaiting()))});
self.addEventListener("activate",e=>{e.waitUntil(caches.keys().then(ks=>Promise.all(ks.filter(k=>k.startsWith("m4terrain")&&k!==CACHE).map(k=>caches.delete(k)))).then(()=>self.clients.claim()))});
self.addEventListener("fetch",e=>{
  if(e.request.method!=="GET")return;
  const u=new URL(e.request.url);if(u.origin!==location.origin)return;
  e.respondWith(caches.match(e.request,{ignoreSearch:true}).then(r=>{
    const reseau=fetch(e.request).then(x=>{if(x&&x.ok)caches.open(CACHE).then(c=>c.put(e.request,x.clone()));return x}).catch(()=>null);
    return r||reseau.then(x=>x||caches.match("./index.html"));
  }));
});
