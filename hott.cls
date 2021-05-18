\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{hott}[2021/05/16 v1.0 Homotopietypentheorie-Skript]

\LoadClass[10pt, twoside]{article}

\RequirePackage[a4paper,margin=2.5cm]{geometry}

\RequirePackage{amsmath,amssymb,mathtools}

% Schönere Tabellen / Auflistungen / Theoreme
\RequirePackage{booktabs}
\RequirePackage{enumerate}
\RequirePackage{enumitem}
\RequirePackage[thmmarks]{ntheorem}

% Verweise + Stichwortverzeicnis
\RequirePackage[linkcolor=black, colorlinks=true, citecolor=black]{hyperref}
\RequirePackage{cleveref}

\RequirePackage{makeidx}

% 
\RequirePackage{polyglossia}
\setdefaultlanguage{german}

% Grafiken
\RequirePackage{tikz}
\usetikzlibrary{arrows, cd}

% Inferenzregeln
\RequirePackage{mathpartir}

% 
\setitemize{topsep=0pt,itemsep=0ex,partopsep=1ex,parsep=1ex}
\setenumerate{topsep=0pt,itemsep=1ex,partopsep=1ex,parsep=1ex}


\theorembodyfont{}
\theoremstyle{break}
    \newtheorem{theorem}{Theorem}[subsection]
    \newtheorem{lemma}[theorem]{Lemma}
    \newtheorem{definition}[theorem]{Definition}
    \newtheorem{bemerkung}[theorem]{Bemerkung}
    \newtheorem{konvention}[theorem]{Konvention}
    \newtheorem{regeln}[theorem]{Regeln}
    \newtheorem{axiom}[theorem]{Axiom}
    \newtheorem{beispiel}[theorem]{Beispiel}

\theoremstyle{nonumberplain}
\theoremsymbol{\ensuremath{\Box}}
    \newtheorem{beweis}{Beweis}

\newcommand{\yields}{\vdash}
\newcommand{\cbar}{\, | \,}
\providecommand*\colonequiv{\vcentcolon\mspace{-1.2mu}\equiv}

\newcommand{\begriff}[1]{\emph{#1}\index{#1}}

% Namen für Regeln
\newcommand{\Weak}{\mathrm{Weak}}
\newcommand{\Var}{\mathrm{Var}}
\newcommand{\Str}{\mathrm{Str}}
\newcommand{\Typ}{\text{ Typ}}
\newcommand{\PiForm}{\Pi\mathrm{F}}
\newcommand{\PiIntro}{\Pi\mathrm{I}}
\newcommand{\PiElim}{\Pi\mathrm{E}}
\newcommand{\PiBeta}{\Pi\beta}
\newcommand{\PiEta}{\Pi\eta}

% Namen für Typen
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\einheit}{\mathbf{1}}
\newcommand{\leer}{\emptyset}
\newcommand{\zwei}{\mathbf{2}}
\newcommand{\isContr}{\mathrm{isContr}}
\newcommand{\isProp}{\mathrm{isProp}}
\newcommand{\isSet}{\mathrm{isSet}}
\newcommand{\isEquiv}{\mathrm{isEquiv}}
\newcommand{\qinv}{\mathrm{qinv}}
\newcommand{\mU}{\mathcal{U}}
\newcommand{\Eq}[1]{\mathrm{Eq}_{#1}}

% Namen für Terme
\newcommand{\ass}{\mathrm{ass}}
\newcommand{\id}{\mathrm{id}}
\newcommand{\ind}[1]{\mathrm{ind}_{#1}}
\newcommand{\rec}[1]{\mathrm{rec}_{#1}}
\newcommand{\sucN}{\mathrm{succ}_{\N}}
\newcommand{\refl}{\mathrm{refl}}
\newcommand{\pair}{\mathrm{pair}}
\newcommand{\kon}{%
    \raisebox{-0.25ex}{\scalebox{1.2}{$\cdot$}}%
}
\newcommand{\FunExt}{\mathrm{FunExt}}
\newcommand{\transp}{\mathrm{tr}}