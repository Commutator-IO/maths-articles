#!/usr/bin/env node
/**
 * Compile chaque `.tex` de `lecons/` en PDF avec Tectonic, dans `dist/`.
 *
 *   npm run pdf              (ignoré, avec un avertissement, si tectonic est absent)
 *   npm run pdf -- --require (échoue si tectonic est absent : c'est le mode de la CI)
 *
 * Tectonic plutôt que TeX Live, comme pour grothendieck-project : un seul
 * binaire, qui ne télécharge que les paquets qu'un document utilise. C'est un
 * moteur XeTeX, donc les documents passent par la branche fontspec/polyglossia
 * de leur préambule.
 *
 * Les PDF sont construits, jamais versionnés (`*.pdf` est dans .gitignore).
 * Lancer ce script avant `npm run render`, pour que les pages pointent vers eux.
 */

import { spawnSync } from 'node:child_process';
import { mkdir, readdir } from 'node:fs/promises';
import { resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '..');
const SOURCE = resolve(ROOT, 'lecons');
const OUT = resolve(ROOT, 'dist', 'lecons');

const probe = spawnSync('tectonic', ['--version'], { encoding: 'utf8' });
if (probe.error) {
  const msg = 'tectonic introuvable — https://tectonic-typesetting.github.io';
  if (process.argv.includes('--require')) {
    process.stderr.write(`${msg}\n`);
    process.exit(1);
  }
  process.stdout.write(`${msg} ; aucun PDF construit.\n`);
  process.exit(0);
}

const failed = [];
let n = 0;
for (const dir of (await readdir(SOURCE, { withFileTypes: true })).filter((d) => d.isDirectory())) {
  for (const f of (await readdir(resolve(SOURCE, dir.name))).filter((x) => x.endsWith('.tex'))) {
    const out = resolve(OUT, dir.name);
    await mkdir(out, { recursive: true });
    const r = spawnSync('tectonic', ['-X', 'compile', '--outdir', out, resolve(SOURCE, dir.name, f)],
      { encoding: 'utf8' });
    if (r.status === 0) {
      n += 1;
      process.stdout.write(`  ✓ ${dir.name}/${f}\n`);
    } else {
      failed.push(`${dir.name}/${f}`);
      process.stderr.write(`  ✗ ${dir.name}/${f}\n${r.stdout}${r.stderr}\n`);
    }
  }
}
process.stdout.write(`${n} PDF → dist/lecons/\n`);
if (failed.length) {
  process.stderr.write(`${failed.length} échec(s) : ${failed.join(', ')}\n`);
  process.exit(1);
}
