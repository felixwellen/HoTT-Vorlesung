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
    \newtheorem{fakt}[theorem]{Fakt}
    \newtheorem{beispiel}[theorem]{Beispiel}

\theoremstyle{nonumberplain}
\theoremsymbol{\ensuremath{\Box}}
    \newtheorem{beweis}{Beweis}

\RequirePackage{../hott}
