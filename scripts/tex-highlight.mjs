/**
 * Coloration syntaxique des sources LaTeX, pour la vue « source LaTeX ».
 *
 * Même principe que scripts/lean-highlight.mjs : une coloration à la
 * construction, en HTML statique, qui ne prétend pas analyser TeX (sa syntaxe
 * change avec les catcodes) mais sépare ce qui aide à lire. Les commentaires,
 * les commandes, les noms d'environnement après \begin et \end, les formules
 * ($…$, \(…\), \[…\] et les environnements mathématiques), les accolades et
 * crochets d'arguments. Les lignes sont numérotées et ancrées (#L12), et une
 * étiquette \label{x} devient la cible #x de ses \ref{x}.
 */

const esc = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
const span = (cls, s) => `<span class="${cls}">${esc(s)}</span>`

// Environnements dont le contenu est mathématique.
const MATH_ENVS = new Set(['equation', 'equation*', 'align', 'align*', 'gather', 'gather*',
  'multline', 'multline*', 'displaymath', 'eqnarray', 'eqnarray*'])

// Commandes de structure, mises en valeur comme des mots-clés.
const STRUCTURE = new Set(['documentclass', 'usepackage', 'section', 'subsection',
  'subsubsection', 'paragraph', 'chapter', 'part', 'begin', 'end', 'item', 'label', 'ref',
  'eqref', 'cite', 'title', 'author', 'date', 'maketitle', 'tableofcontents', 'input',
  'newcommand', 'renewcommand', 'DeclareMathOperator', 'newtheorem', 'theoremstyle',
  'bibitem', 'caption'])

/**
 * Colorie le fichier entier. L'état « en mode mathématique » traverse les
 * lignes (une formule display s'étend souvent sur plusieurs lignes) ; on le
 * suit avec le délimiteur qui doit la fermer.
 */
export function highlightTex(source) {
  const lines = source.replace(/\n$/, '').split('\n')
  let mathEnd = null // '$', '$$', '\\)', '\\]', ou '\\end{env}'
  const out = []

  for (let k = 0; k < lines.length; k++) {
    const ligne = lines[k]
    let html = ''
    let i = 0
    while (i < ligne.length) {
      const reste = ligne.slice(i)

      // Commentaire : % non échappé, jusqu'au bout de la ligne.
      if (reste[0] === '%') { html += span('tex-com', reste); break }

      if (mathEnd) {
        // En mode mathématique : avancer jusqu'à la fermeture, en gardant
        // les commentaires.
        let j = i
        let ferme = -1
        while (j < ligne.length) {
          if (ligne[j] === '\\' && ligne.startsWith(mathEnd, j) && mathEnd !== '$' && mathEnd !== '$$') { ferme = j; break }
          if (ligne[j] === '\\') { j += 2; continue }
          if (ligne[j] === '%') break
          if ((mathEnd === '$' || mathEnd === '$$') && ligne.startsWith(mathEnd, j)) { ferme = j; break }
          j++
        }
        if (ferme === -1) { html += span('tex-math', ligne.slice(i, j)); i = j; continue }
        html += span('tex-math', ligne.slice(i, ferme))
        if (mathEnd.startsWith('\\end{')) {
          html += span('tex-kw', '\\end') + span('tex-brace', '{') + span('tex-env', mathEnd.slice(5, -1)) + span('tex-brace', '}')
        } else {
          html += span('tex-delim', mathEnd)
        }
        i = ferme + mathEnd.length
        mathEnd = null
        continue
      }

      // Ouvertures de formules.
      if (reste.startsWith('$$')) { html += span('tex-delim', '$$'); mathEnd = '$$'; i += 2; continue }
      if (reste[0] === '$') { html += span('tex-delim', '$'); mathEnd = '$'; i += 1; continue }
      if (reste.startsWith('\\(')) { html += span('tex-delim', '\\('); mathEnd = '\\)'; i += 2; continue }
      if (reste.startsWith('\\[')) { html += span('tex-delim', '\\['); mathEnd = '\\]'; i += 2; continue }

      // \begin{env} et \end{env}.
      const env = /^\\(begin|end)\{([^}]*)\}/.exec(reste)
      if (env) {
        html += span('tex-kw', `\\${env[1]}`) + span('tex-brace', '{') + span('tex-env', env[2]) + span('tex-brace', '}')
        i += env[0].length
        if (env[1] === 'begin' && MATH_ENVS.has(env[2])) mathEnd = `\\end{${env[2]}}`
        continue
      }

      // \label{x} : une ancre, que les \ref{x} visent.
      const lab = /^\\(label|ref|eqref)\{([^}]*)\}/.exec(reste)
      if (lab) {
        const cible = esc(lab[2])
        const nom = lab[1] === 'label'
          ? `<span class="tex-label" id="${cible.replace(/"/g, '&quot;')}">${cible}</span>`
          : `<a class="tex-ref" href="#${encodeURIComponent(lab[2])}">${cible}</a>`
        html += span('tex-kw', `\\${lab[1]}`) + span('tex-brace', '{') + nom + span('tex-brace', '}')
        i += lab[0].length
        continue
      }

      // Une commande : \mot, ou \ suivi d'un seul caractère.
      const cmd = /^\\([A-Za-z@]+\*?|.)/.exec(reste)
      if (cmd) {
        html += span(STRUCTURE.has(cmd[1]) ? 'tex-kw' : 'tex-cmd', cmd[0])
        i += cmd[0].length
        continue
      }

      if ('{}[]'.includes(reste[0])) { html += span('tex-brace', reste[0]); i++; continue }

      // Texte ordinaire, d'un bloc jusqu'au prochain caractère spécial.
      const texte = /^[^\\%${}[\]]+/.exec(reste)
      if (texte) { html += esc(texte[0]); i += texte[0].length; continue }
      html += esc(reste[0])
      i++
    }
    const n = k + 1
    out.push(`<span class="src-line" id="L${n}"><a class="src-ln" href="#L${n}">${n}</a>${html || ' '}</span>`)
  }
  return out.join('')
}

export const TEX_STYLE = `
  pre.tex { white-space: pre-wrap; word-break: break-word; }
  .src-line { display: block; padding-left: 5.4ch; text-indent: -5.4ch; }
  .src-line:target, .tex-label:target { background: #fdf6dc; }
  .src-ln { display: inline-block; width: 4ch; margin-right: 1.4ch; text-align: right; text-indent: 0;
            color: var(--ink4); text-decoration: none; user-select: none; }
  .src-ln:hover { color: var(--accent); }
  .tex-com { color: var(--ink3); font-style: italic; }
  .tex-kw { color: var(--accent); font-weight: 600; }
  .tex-cmd { color: #2d4f86; }
  .tex-env { color: #0e6744; font-weight: 600; }
  .tex-math { color: #8a3b1e; }
  .tex-delim { color: #8a3b1e; font-weight: 600; }
  .tex-brace { color: var(--ink4); }
  .tex-label { color: #0e6744; }
  .tex-ref { color: #0e6744; text-decoration: none; }
  .tex-ref:hover { text-decoration: underline dotted; text-underline-offset: 2px; }
`
