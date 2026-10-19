#!/usr/bin/env node
/**
 * Serveur local : construit `dist/`, le sert sur http://localhost:4173, et
 * reconstruit à chaque modification sous `lecons/`, `scripts/` ou `public/`.
 *
 *   npm run dev
 *
 * Un fichier refusé par le moteur affiche l'erreur dans le terminal ; les
 * autres pages restent servies.
 */

import { createServer } from 'node:http';
import { readFile, stat } from 'node:fs/promises';
import { watch } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { extname, resolve, sep } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const DIST = resolve(ROOT, 'dist');
const PORT = Number(process.env.PORT ?? 4173);

const TYPES = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.woff2': 'font/woff2',
  '.pdf': 'application/pdf',
  '.svg': 'image/svg+xml',
  '.tex': 'text/plain; charset=utf-8',
  '.lean': 'text/plain; charset=utf-8',
};

const build = () => spawnSync(process.execPath, [resolve(ROOT, 'scripts', 'render.mjs')], { stdio: 'inherit' });
build();

let timer;
for (const dir of ['lecons', 'scripts', 'public']) {
  watch(resolve(ROOT, dir), { recursive: true }, () => {
    clearTimeout(timer);
    timer = setTimeout(build, 150);
  });
}
watch(resolve(ROOT, 'lecons.json'), () => build());

createServer(async (req, res) => {
  const path = decodeURIComponent(new URL(req.url, 'http://x').pathname);
  let file = resolve(DIST, `.${path}`);
  if (file !== DIST && !file.startsWith(DIST + sep)) {
    res.writeHead(403).end();
    return;
  }
  try {
    if ((await stat(file)).isDirectory()) file = resolve(file, 'index.html');
    const body = await readFile(file);
    res.writeHead(200, { 'content-type': TYPES[extname(file)] ?? 'application/octet-stream', 'cache-control': 'no-store' });
    res.end(body);
  } catch {
    res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' }).end('Introuvable');
  }
}).listen(PORT, () => process.stdout.write(`http://localhost:${PORT}/\n`));
