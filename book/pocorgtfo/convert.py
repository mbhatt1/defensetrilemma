#!/usr/bin/env python3
# Convert the TrilemmaBook Verso sources into a PoC||GTFO-styled, KDP-ready book.
# Light-touch gospel voice: per-chapter Pastor's prefaces + front matter; the
# technical body (prose, proofs, Lean) is transcribed verbatim.
import glob, re, os

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = sorted(glob.glob(os.path.join(HERE, "..", "TrilemmaBook", "Ch*.lean")))

#------------------  unicode maps
MATH = {
 '→':r'\rightarrow','↦':r'\mapsto','↔':r'\leftrightarrow','←':r'\leftarrow',
 '∀':r'\forall','∃':r'\exists','¬':r'\lnot','∈':r'\in','∉':r'\notin',
 '∧':r'\land','∨':r'\lor','∘':r'\circ','∩':r'\cap','∪':r'\cup','∅':r'\emptyset',
 '⊆':r'\subseteq','⊢':r'\vdash','⊬':r'\nvdash','⊥':r'\bot',
 '≤':r'\leq','≥':r'\geq','≠':r'\neq','≈':r'\approx','≫':r'\gg',
 '×':r'\times','·':r'\cdot','−':r'-','∞':r'\infty','√':r'\surd','∫':r'\int',
 '∂':r'\partial','∇':r'\nabla','∑':r'\sum','∎':r'\blacksquare',
 '⟨':r'\langle','⟩':r'\rangle','⌜':r'\ulcorner','⌝':r'\urcorner',
 '⌈':r'\lceil','⌉':r'\rceil','‖':r'\|',
 'ℝ':r'\mathbb{R}','ℕ':r'\mathbb{N}','ℓ':r'\ell',
 'ε':r'\varepsilon','δ':r'\delta','τ':r'\tau','γ':r'\gamma','φ':r'\varphi',
 'μ':r'\mu','σ':r'\sigma','θ':r'\theta','α':r'\alpha','ψ':r'\psi','κ':r'\kappa',
 'χ':r'\chi','π':r'\pi','ρ':r'\rho','Σ':r'\Sigma','Π':r'\Pi','Γ':r'\Gamma',
 '₀':r'_0','₁':r'_1','₂':r'_2','ₙ':r'_n','ᵢ':r'_i','ₗ':r'_l','₋':r'_-','₊':r'_+',
 '¹':r'^1','²':r'^2','ⁿ':r'^n','⁻':r'^-','⁺':r'^+',
}
TEXT = {'ö':r'\"o','Ö':r'\"O','ä':r'\"a','ü':r'\"u','Ü':r'\"U','é':r"\'e",
        '–':'--','…':r'\ldots{}'}
SPECIAL = {'&':r'\&','%':r'\%','#':r'\#','_':r'\_','^':r'\textasciicircum{}',
           '~':r'\textasciitilde{}','{':r'\{','}':r'\}','$':r'\$',
           '\\':r'\textbackslash{}'}

def map_unicode(s):
    return ''.join('\\('+MATH[c]+'\\)' if c in MATH else TEXT.get(c,c) for c in s)

def esc_text(s):
    s = re.sub(r'([A-Za-z])\u0302', lambda m: '\\(\\hat{%s}\\)'%m.group(1), s)
    s = s.replace('\u0302','')
    s = s.replace('\\_','\x00UND\x00').replace('\\ ',' ')
    s = ''.join(SPECIAL.get(c,c) for c in s)
    # convert straight double quotes BEFORE unicode mapping, or the quote step
    # would corrupt the " inside accents like \"o (umlaut) that map_unicode adds
    s = re.sub(r'(^|[\s(\[])"', r"\1``", s)
    s = s.replace('"', "''")
    s = map_unicode(s)
    s = s.replace('\x00UND\x00', r'\_')
    return s

def code_inline(s):
    s = re.sub(r'(.)\u0302', r'\1', s)
    s = s.replace('\\_','_')
    s = ''.join(SPECIAL.get(c,c) for c in s)
    s = map_unicode(s)
    s = s.replace('\\_', '\\_\\allowbreak{}')     # let snake_case wrap
    return r'\texttt{'+s+'}'

def emph(s):
    out=[]; pos=0
    pat=re.compile(r'\*([^*]+)\*|(?<![A-Za-z0-9\\])_([^_]+)_(?![A-Za-z0-9])')
    for m in pat.finditer(s):
        out.append(esc_text(s[pos:m.start()]))
        inner = m.group(1) if m.group(1) is not None else m.group(2)
        out.append(r'\emph{'+esc_text(inner)+'}')
        pos=m.end()
    out.append(esc_text(s[pos:]))
    return ''.join(out)

_EM = re.compile(r'\*([^*]+)\*'
                 r'|(?<![A-Za-z0-9\\])_([^_]+)_(?![A-Za-z0-9])')
def inline(s):
    # Protect inline code spans FIRST (so underscores/asterisks inside code, e.g.
    # `φ_e`, cannot break emphasis matching), then tokenize *..* / _.._ emphasis,
    # then restore the code. Emphasis may contain code; the placeholder carries it.
    s = re.sub(r'\{[a-zA-Z]+\}(?=`)', '', s)          # drop Verso role prefix {lean}`x`
    codes=[]
    def _stash(m): codes.append(m.group(1)); return '\x01%d\x01'%(len(codes)-1)
    s = re.sub(r'`([^`]*)`', _stash, s)
    def render(t):                                     # restore code chips, escape text
        parts=re.split('\x01(\\d+)\x01', t); r=[]
        for i,p in enumerate(parts):
            r.append(code_inline(codes[int(p)]) if i%2 else esc_text(p))
        return ''.join(r)
    out=[]; pos=0
    for m in _EM.finditer(s):
        out.append(render(s[pos:m.start()]))
        inner=m.group(1) if m.group(1) is not None else m.group(2)
        out.append(r'\emph{'+render(inner)+'}')
        pos=m.end()
    out.append(render(s[pos:]))
    return ''.join(out)

_LABELKW = (r'Definition|Theorem|Lemma|Corollary|Proposition|Remark|Example|'
            r'Exercise|Proof|Fact|Claim|Notation|Convention|Algorithm')
LABEL = re.compile(r'^(' + _LABELKW + r')(\s+[\d.]+[a-z]?)?(\s*\([^)]*\))?\.')
# emphasis-wrapped label, e.g. "*Definition 1.1 (System).*" (source's usual form)
EMPH_LABEL = re.compile(r'\*((?:' + _LABELKW + r')[^*]*)\*\s*')

def para(text, dropcap=False):
    text = text.strip()
    if dropcap:
        dm = re.match(r'([A-Za-z])([A-Za-z]*)', text)
        if dm:
            return (r'\par\noindent\lettrine[lines=3,findent=2pt,nindent=6pt]{'
                    + dm.group(1) + '}{' + dm.group(2) + '}'
                    + inline(text[dm.end():]))
    em = EMPH_LABEL.match(text)
    if em:
        return r'\vp \textbf{'+inline(em.group(1))+'}'+inline(text[em.end():])
    m = LABEL.match(text)
    if m:
        return r'\vp \textbf{'+inline(m.group(0))+'}'+inline(text[m.end():])
    return r'\vp '+inline(text)

def heading(level, text):
    cmd = {1:'section',2:'subsection',3:'subsubsection'}[level]
    return '\\'+cmd+'{'+inline(text.strip())+'}'

def code_block(lines):
    lines=[re.sub(r'(.)\u0302', r'\1', l) for l in lines]
    return '\\begin{poc}\n\\begin{lstlisting}\n'+'\n'.join(lines)+'\n\\end{lstlisting}\n\\end{poc}'

def _cells(r):
    r=r.strip()
    if r.startswith('|'): r=r[1:]
    if r.endswith('|'): r=r[:-1]
    return [c.strip() for c in r.split('|')]

def md_table(lines):
    def is_sep(r): return set(r.strip()) <= set('|-: ') and '-' in r
    rows=[_cells(r) for r in lines if r.strip().startswith('|') and not is_sep(r)]
    ncol=max(len(r) for r in rows)
    spec='|'+'X|'*ncol
    out=['\\begin{center}\\scriptsize\\setlength{\\tabcolsep}{4pt}',
         '\\begin{tabularx}{\\linewidth}{'+spec+'}','\\hline']
    for i,r in enumerate(rows):
        r=r+['']*(ncol-len(r))
        cellcmd=(lambda c:'\\textbf{'+inline(c)+'}') if i==0 else inline
        out.append(' & '.join(cellcmd(c) for c in r)+' \\\\ \\hline')
    out+=['\\end{tabularx}','\\end{center}']
    return '\n'.join(out)

def listitem_split(lines, marker):
    items=[]; cur=None
    for l in lines:
        m=marker.match(l)
        if m:
            if cur is not None: items.append(cur)
            cur=l[m.end():].strip()
        else:
            cur=(cur+' '+l.strip()) if cur else l.strip()
    if cur is not None: items.append(cur)
    return items

#------------------  prefaces
PREFACE = {
"Ch00_Preliminaries":
 r"Before the preaching, the catechism. Here you learn to read the kernel's own "
 r"hand: the handful of constructs every proof in this gospel is built from, and "
 r"the one command, \texttt{\#print axioms}, that tells you exactly what a theorem "
 r"costs. Read it slowly. The Pastor promises this is the last time you must look "
 r"anything up.",
"Ch01_Diagonal":
 r"This is the engine, and it is older than all of us: Lawvere, in the year 1969. "
 r"One move, name your own behavior, then build the description that disagrees "
 r"with you about yourself, and five famous ghosts step out of a single coffin. "
 r"Learn these five lines and you can read every proof that follows.",
"Ch02_ClassicalLimits":
 r"Cantor, Russell, G\"odel, Tarski, Turing. Five heresies the last century burned "
 r"on five separate stakes, confessed here to be one. Watch the same diagonal walk "
 r"through set theory, logic, and computation in different robes, and you will "
 r"never again mistake them for cousins. They are the same saint.",
"Ch03_Trilemmata":
 r"Here is the scandal of the gospel. Three AI-safety impossibilities, published "
 r"apart and proved apart, are one proof term, equal, the kernel says, by "
 r"\texttt{rfl}. The Pastor does not charge the three authors with error; he "
 r"testifies only that the machine sees one theorem where the literature saw "
 r"three. Grade the premise, not the proof.",
"Ch04_FromLogicToAnalysis":
 r"When a system will not name itself, the diagonal has nothing to bite. So the "
 r"gospel keeps a second engine. Give it a connected space and a continuous field, "
 r"and the intermediate value theorem walks you to the very same wall, now with a "
 r"width you can measure. One fixed point, sitting at one-half, is the whole "
 r"difference between the two engines.",
"Ch05_AttackGeometry":
 r"The diagonal swears the bad point exists; it will not say how far away it sits. "
 r"This sermon is where the number lives: basins, Lipschitz tubes, and the boundary "
 r"density of your real traffic. Here existence becomes geometry, and geometry "
 r"becomes a budget an adversary is free to spend.",
"Ch06_ApproximateBridges":
 r"The sharp theorems assume a world of exact calibration and perfect separation. "
 r"The world is not exact. This sermon prices the slack: what survives when the "
 r"hypotheses hold only up to \(\varepsilon\), and why the truth slack can be "
 r"shrunk toward zero but never closed.",
"Ch07_AISafety":
 r"Now the altar call, for the engineer. The impossibility is not a wall but a "
 r"menu: three corners, abstain, price a band, or decouple, and no fourth. Choose "
 r"your corner on purpose. And mind the three sentences in this sermon that confess "
 r"\emph{Not formalized}; they are deployment counsel, not theorems, and the Pastor "
 r"will not pretend otherwise.",
"Ch08_JSpace":
 r"The standing objection says all of this concerns outputs only. This sermon "
 r"answers it, turning both engines on a probe that reads the derivative of the "
 r"computation rather than its words. The middle of the machine is no sanctuary: "
 r"the diagonal and the intermediate value theorem are already waiting there.",
"Ch09_CoTMonitoring":
 r"Read the chain of thought, they say, and you will catch the machine in the act. "
 r"But the trace is text the model chose to emit: faithfulness forces it to be "
 r"long, and selection quietly destroys the signal. This sermon asks what a monitor "
 r"can honestly see.",
"Ch10_LatentKnowledge":
 r"Eliciting latent knowledge, ask the reporter what the model really knows. The "
 r"obstruction here is not the diagonal at all, but a plain counting fact about "
 r"functions that agree on a subset. The reporter is underdetermined, and no "
 r"cleverness closes a gap the data itself left open.",
"Ch11_Watermarking":
 r"Leave the model entirely. A watermark is a promise of invariance under "
 r"paraphrase, and paraphrase is only an adversary with a thesaurus. This sermon "
 r"reaches the third corner of detection with no self-reference at all.",
"Ch12_Appendices":
 r"The back of the hymnal: the build, the axiom audit, and the full accounting of "
 r"what is proved, what is cited, and what is merely counsel. If you distrust a "
 r"single line of this gospel, here is where you learn to make the kernel repeat "
 r"it back to you.",
}

def convert_chapter(path):
    base = os.path.splitext(os.path.basename(path))[0]
    raw=open(path,encoding='utf-8').read().split('\n')
    title=None; start=0
    for i,l in enumerate(raw):
        m=re.match(r'#doc \(Manual\) "(.*)" =>', l)
        if m: title=m.group(1); start=i+1; break
    lines=raw[start:]
    blocks=[]; buf=[]; infence=False; fbuf=[]; inmeta=False
    for l in lines:
        if inmeta:
            if l.strip()=='%%%': inmeta=False
            continue
        if not infence and l.strip()=='%%%':
            if buf: blocks.append(('text',buf)); buf=[]
            inmeta=True; continue
        if not infence and l.startswith('```'):
            if buf: blocks.append(('text',buf)); buf=[]
            infence=True; fbuf=[]; continue
        if infence:
            if l.startswith('```'):
                blocks.append(('code',fbuf)); infence=False
            else: fbuf.append(l)
            continue
        if l.strip()=='':
            if buf: blocks.append(('text',buf)); buf=[]
        else:
            buf.append(l)
    if buf: blocks.append(('text',buf))

    out=['\\chapter{'+inline(title)+'}']
    if base in PREFACE:
        out.append('\\begin{pastor}\n'+PREFACE[base]+'\n\\end{pastor}')
    dropcap_pending=True
    bullet=re.compile(r'^\s*[*-]\s+'); num=re.compile(r'^\s*\d+\.\s+')
    for kind,data in blocks:
        if kind=='code':
            out.append(code_block(data)); continue
        if not any(x.strip() for x in data):     # skip empty blocks
            continue
        first=data[0]
        hm=re.match(r'(#{1,3})\s+(.*)', first)
        if hm:
            out.append(heading(len(hm.group(1)), hm.group(2)))
            rest=[x for x in data[1:] if x.strip()]
            if rest: out.append(para(' '.join(rest)))
            continue
        if (first.strip().startswith('|') and len(data)>1
                and set(data[1].strip()) <= set('|-: ') and '-' in data[1]):
            out.append(md_table(data)); continue
        if bullet.match(first):
            out.append('\\begin{itemize}')
            for it in listitem_split(data, bullet): out.append('\\item '+inline(it))
            out.append('\\end{itemize}'); continue
        if num.match(first):
            out.append('\\begin{enumerate}')
            for it in listitem_split(data, num): out.append('\\item '+inline(it))
            out.append('\\end{enumerate}'); continue
        text=' '.join(data)
        if dropcap_pending and not text.lstrip().startswith('*') and re.match(r'[A-Za-z]', text.strip()):
            out.append(para(text, dropcap=True)); dropcap_pending=False
        else:
            out.append(para(text))
    return '\n\n'.join(out)

BODY='\n\n'.join(convert_chapter(p) for p in SRC)
# Homage-only wording tweaks (source chapters are left untouched): neutralize the
# two thesis-prose uses of the literal phrase, preserving the exact meaning.
for _a,_b in [("the one diagonal pattern","the single diagonal pattern"),
              (r"the \emph{one} diagonal pattern", r"the \emph{single} diagonal pattern"),
              ("is one diagonal, and the three trilemmata are it",
               "is a single diagonal, and the three trilemmata are it")]:
    BODY=BODY.replace(_a,_b)
# Copyedit fixes found by the systematic review (homage layer; canonical sources
# untouched). Each is an objective typo correction that preserves meaning.
COPYEDIT=[
    ("nonneglible","nonnegligible"),                                   # Ch8 typo
    # three section cross-references that each point one section too high,
    # verified against the chapters' heading structure:
    ("measurement protocol of Section 6 histograms",                   # Ch7: ->5
     "measurement protocol of Section 5 histograms"),
    ("counterpart to the warning of Section 3",                        # Ch7: ->2
     "counterpart to the warning of Section 2"),
    ("worked corner example of Section 6",                             # Ch5: ->5
     "worked corner example of Section 5"),
]
for _a,_b in COPYEDIT:
    if _a in BODY:            # now also fixed at source; tolerant no-op if absent
        BODY=BODY.replace(_a,_b)

LITERATE=' '.join('{'+c+'}{{$'+l+'$}}1' for c,l in MATH.items())

PREAMBLE=r'''\documentclass[12pt,twoside,openright]{book}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[paperwidth=6in,paperheight=9in,top=0.8in,bottom=0.8in,
            inner=0.9in,outer=0.6in]{geometry}
\usepackage{mathpazo}
\usepackage{inconsolata}
\usepackage{microtype}
\usepackage{amsmath,amssymb}
\usepackage{xcolor}
\usepackage{graphicx}
\usepackage{tikz}
\usetikzlibrary{decorations.text,decorations.pathmorphing,arrows.meta}
\usepackage{tabularx}
\usepackage{lettrine}
\usepackage{titlesec}
\usepackage{fancyhdr}
\usepackage{listings}
\usepackage[most]{tcolorbox}
\usepackage{pifont}
\usepackage{emptypage}
\linespread{1.12}

\definecolor{ink}{gray}{0.10}
\definecolor{deepgray}{gray}{0.40}
\definecolor{rule}{gray}{0.0}
\definecolor{boxback}{gray}{0.96}
\definecolor{bloodred}{RGB}{140,20,20}
\color{ink}

\newcommand{\pp}{\ensuremath{\mathbin{\|}}}
\newcommand{\manicule}{\ding{43}}
\newcommand{\motto}{\(f\,a_0\,a_0 = \lnot(f\,a_0\,a_0)\)}

\newcounter{verse}[chapter]
\newcommand{\vp}{\par\refstepcounter{verse}\noindent
  \textbf{\scriptsize\thechapter:\theverse}\hspace{0.45em}\ignorespaces}

\titleformat{\chapter}[display]
  {\normalfont\filleft\scshape}{\large Sermon \thechapter}{0.5em}
  {\Huge\bfseries\itshape}
  [\vspace{0.35em}{\color{rule}\titlerule[1.1pt]}]
\titlespacing*{\chapter}{0pt}{12pt}{22pt}
\titleformat{\section}{\normalfont\large\bfseries}{\thesection}{0.6em}{}
\titleformat{\subsection}{\normalfont\bfseries}{\thesubsection}{0.6em}{}
\titleformat{\subsubsection}{\normalfont\bfseries\itshape}{}{0em}{}
\setcounter{secnumdepth}{2}
\setcounter{tocdepth}{0}

\fancypagestyle{tent}{%
  \fancyhf{}%
  \fancyhead[LE]{\scshape\footnotesize Pick Two}%
  \fancyhead[RO]{\scshape\footnotesize\nouppercase{\leftmark}}%
  \fancyfoot[C]{\small\thepage}%
  \renewcommand{\headrulewidth}{0.3pt}}
\renewcommand{\chaptermark}[1]{\markboth{#1}{#1}}
\pagestyle{tent}

\newtcolorbox{poc}{%
  breakable, enhanced, sharp corners, boxrule=0.7pt, colback=boxback,
  colframe=rule, left=4pt,right=4pt,top=3pt,bottom=3pt,
  before skip=7pt, after skip=7pt,
  overlay unbroken and first={\node[anchor=north east,font=\tiny\scshape,
     text=white, fill=rule, inner xsep=4pt, inner ysep=1.5pt]
     at (frame.north east) {Proof of Concept \ding{51}\ kernel-checked};}}

\newtcolorbox{caution}[1][A Caution to the Zealous]{%
  breakable, enhanced, sharp corners, boxrule=0.7pt, colback=boxback,
  colframe=rule, coltitle=white, left=7pt,right=7pt,top=5pt,bottom=5pt,
  fonttitle=\bfseries\scshape, title={\manicule\ #1}}

\newtcolorbox{pastor}{%
  blanker, breakable, left=1.1em, right=0.6em, before skip=2pt, after skip=12pt,
  borderline west={1.3pt}{0pt}{bloodred},
  fontupper=\itshape\small\color{ink!88}}

\lstdefinelanguage{lean}{
  morekeywords={theorem,def,lemma,example,match,with,fun,by,decide,inductive,
    where,structure,Prop,Type,Bool,Nat,Int,Unit,True,False,Or,And,Exists,Option,
    refine,have,exact,intro,induction,omega,rcases,funext,congr,obtain,absurd,
    namespace,open,instance,class,variable,let,calc,show,from,this,at,using,
    simp,rfl,constructor,apply,cases,rintro,abbrev,notation},
  sensitive=true, morecomment=[l]{--}, morecomment=[s]{/-}{-/}, morestring=[b]",
}
\lstset{
  language=lean, basicstyle=\footnotesize\ttfamily, keywordstyle=\bfseries,
  commentstyle=\itshape\color{deepgray}, columns=fullflexible, keepspaces=true,
  showstringspaces=false, inputencoding=utf8, extendedchars=true,
  breaklines=true, breakatwhitespace=false, breakindent=1.2em,
  literate=@LITERATE@
}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.42em}
\emergencystretch=4em
% a parskip book must not force-fill pages, or inter-paragraph glue stretches
% into uneven vertical gaps; ragged bottoms keep spacing uniform
\raggedbottom
\clubpenalty=10000
\widowpenalty=10000
\displaywidowpenalty=10000
\hyphenpenalty=1200

\begin{document}
'''.replace('@LITERATE@', LITERATE)

SUBTITLE = r"The Three Promises No Machine Keeps at Once"

EMBLEM=r'''\begin{tikzpicture}[scale=#SCALE#]
  \draw[line width=1.1pt,#FG#] (0,0) circle (3.0cm);
  \draw[line width=0.5pt,#FG#] (0,0) circle (2.82cm);
  \path[decorate,decoration={text along path,text align=center,
        text={|\scshape\small\color{#FG#}|NO UNIVERSAL VERDICT  --  PROVE IT OR GET OUT  -- }}]
        (0,0) ++(180:2.9cm) arc (180:-180:2.9cm);
  % the diagonal motif, kept clear of the centre text (which masks it)
  \draw[line width=0.8pt,#FG#,dash pattern=on 3pt off 2.5pt] (-1.3,-1.3) -- (1.3,1.3);
  \fill[#FG#] (1.3,1.3) circle (1.6pt);
  \node[#FG#,anchor=south west,font=\scriptsize,inner sep=1pt] at (1.3,1.24) {$a_0$};
  % clean ouroboros ring, well outside the centre text
  \draw[line width=2.6pt,bloodred,-{Stealth[length=4.5mm]}]
        (104:1.98cm) arc (104:-250:1.98cm);
  % centre text on opaque chips so nothing can clobber it
  \node[fill=#EMBG#,text=#FG#,inner sep=2pt,font=\itshape] at (0,0.46) {the liar};
  \node[fill=#EMBG#,text=#FG#,inner sep=2pt,font=\footnotesize] at (0,-0.1) {\motto};
\end{tikzpicture}'''

FRONT=r'''
\frontmatter
%, - half-title
\thispagestyle{empty}
\vspace*{2.2in}
\begin{center}{\fontsize{30}{34}\selectfont\bfseries Pick Two}\end{center}
\clearpage\thispagestyle{empty}\cleardoublepage
%, - title page
\thispagestyle{empty}
\begin{center}
{\scshape\small an epistle to the neighborly builders of oracles}\\[0.5em]
{\color{rule}\rule{\linewidth}{1.3pt}}\\[0.4em]
{\fontsize{34}{38}\selectfont\bfseries Pick Two}\\[0.5em]
{\itshape \SUBTITLE}\\[0.4em]
{\color{rule}\rule{\linewidth}{1.3pt}}\\[1.1em]
{\scshape Issue 0x01}\\[1.6em]
\EMBLEMBIG\\[1.6em]
{\small by \textsc{Manish Bhatt}}\\[0.6em]
{\footnotesize compiled, and preached, by M.~Bhatt}\\[1.6em]
{\scshape Shrewd Research}
\end{center}
\clearpage
%, - copyright / colophon-recto
\thispagestyle{empty}
\footnotesize\raggedright
\textbf{Pick Two}, Issue 0x01. First printing, 2026.
Published by \textsc{Shrewd Research}.

\medskip
This volume is made in the spirit of the hacker zines. It is not affiliated with,
endorsed by, or originating from any other publication, and borrows no one's
trade dress.

\medskip
The mathematical content, and every Lean proof reproduced herein, is the work of Manish Bhatt. Every numbered result
is either machine-checked in Lean~4 or carries a citation that resolves to a
checked declaration; the three deployment claims that are not proved say so in
the words \emph{Not formalized}.

\medskip
All proofs are elaborated by Lean~4 and are \texttt{sorry}-free. The combinatorial
core is axiom-free; the analytic results rest only on the three standard kernel
axioms \texttt{propext}, \texttt{Classical.choice}, and \texttt{Quot.sound}.

\medskip
The full text is available free as a PDF. If you paid for this object, you bought
the object, and the Pastor thanks you. Share the ideas freely.

\medskip
Set in Palatino and Inconsolata; typeset with pdf\LaTeX.\\
\textsc{isbn} 979-8-0000000-0-0 \ (placeholder).\\
\emph{Soli kernel gloria.} \quad Prove it, or get out.
\cleardoublepage
%, - foreword
\chapter*{Please Stand: The Pastor Opens the Tent}
\addcontentsline{toc}{chapter}{Please Stand: The Pastor Opens the Tent}
\markboth{The Pastor Opens the Tent}{The Pastor Opens the Tent}

\lettrine[lines=3]{H}{owdy}, neighbors, and welcome under the canvas. You came to
build an oracle that is \emph{honest}, that is \emph{calibrated}, and that
\emph{answers}. The Pastor has bad news, and it is the best kind of bad news,
because it is a theorem and not an opinion.

There is one heresy worth burning: the belief that with enough scale and enough
cleverness you will one day ship a machine that is faithful, calibrated, and
covering all at once, over questions it can be asked about itself. You will not.
Not because you are not clever, because the point where all three hold does not
exist, and a small program a few thousand lines long, the kernel, will say so
without blinking.

This is not a wall. A wall says stop. This is a \emph{menu}, and its whole value
is that the list has exactly three items and there is no fourth. Every oracle that must answer
about itself already sits at one of three corners, most of them by accident. The
gospel that follows makes the choice deliberate.

And here is what makes it a Proof of Concept and not a sermon only: the proofs
are machine-checked. Elaborated by Lean~4, checked by its kernel, audited for the
axioms they lean on. When this book says a thing is proven, a referee you can
download has already agreed. When it has \emph{not} proven a thing, and there are
exactly three such sentences, all about deployment cost, it confesses in the open,
in the only words we accept: \emph{Not formalized}.

A word of honest disclaimer the Pastor owes you before you give an offering. The
engine at the bottom of all of this is Lawvere's fixed-point theorem, and it is
from 1969. We invented none of it. The novelty, such as it is, lives entirely in
the \emph{reading}: the argument that a real oracle, a real defense, a real probe
is the kind of self-naming thing the ancient theorem already forbids. The proof
is one line. The modeling is the whole book, and the modeling is where an honest
neighbor is free to disagree. These are results about what \emph{exists}, not
about how \emph{often} you will meet it. Hold that, and read on.

\vspace{0.4em}\hfill\emph{The Pastor}
\cleardoublepage
\tableofcontents
\mainmatter
\setcounter{chapter}{-1}
'''.replace('\\SUBTITLE', SUBTITLE)\
   .replace('\\EMBLEMBIG', EMBLEM.replace('#SCALE#','0.72').replace('#FG#','ink').replace('#EMBG#','white'))

COLOPHON=r'''
\backmatter
\chapter*{Colophon \& Benediction}
\addcontentsline{toc}{chapter}{Colophon \& Benediction}
\markboth{Colophon}{Colophon}

Every word and every Lean block in this volume is the work of Manish Bhatt.
The combinatorial core is axiom-free; the analytic refinements rest on the three
standard kernel axioms \texttt{propext}, \texttt{Classical.choice}, and
\texttt{Quot.sound}. The companion corpus is four Lake packages, ninety-four
authored source files, some seventeen thousand lines, and no \texttt{sorry}.

The full \texttt{lake build} was re-run for this printing. All four packages
compile green and \texttt{sorry}-free (8072 build jobs in the geometry package
alone), and the axiom audit prints as the creed promises: the diagonal engine,
the \texttt{rfl} unification, and \texttt{no\_reflective\_verdict} depend on
\emph{no} axioms, while every analytic result depends on exactly
\texttt{propext}, \texttt{Classical.choice}, and \texttt{Quot.sound}. This is an
ordinary PDF, not a polyglot; that is the one zine tradition it does not
keep.

\vspace{1.2em}
\begin{center}
The three trilemmata are one theorem, seen from three domains.\\
The proof is a line, the modeling is the work, and the kernel is the referee.\\[1.0em]
{\itshape Do the proof, or get the heretics out.}\\[0.3em]
{\bfseries\large Prove It, or Get Out.}\\[0.6em]
\emph{Amen.}
\end{center}
% pad to an even page count so the printed paperback ends cleanly
\clearpage
\ifodd\value{page}\else
  \thispagestyle{empty}\null\clearpage
\fi
\end{document}
'''

open(os.path.join(HERE,'aipocorgtfo-book.tex'),'w',encoding='utf-8').write(
    PREAMBLE+FRONT+BODY+COLOPHON)
print("wrote aipocorgtfo-book.tex")
