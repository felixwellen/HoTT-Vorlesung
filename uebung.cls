% latex -xelatex -pdf uebung??.tex
\ProvidesClass{uebung}
\LoadClass[a4paper]{article}

\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{enumitem}
\RequirePackage{geometry}
\RequirePackage{hott}
\RequirePackage{mathpartir}
\RequirePackage{mathtools}
\RequirePackage{tikz-cd}

\geometry{top=2.5cm}
\setlength{\parindent}{0pt}
\setlength{\parskip}{\medskipamount}
\setenumerate[1]{label=(\alph*),topsep=0pt}
\setenumerate[2]{label=(\roman*),topsep=0pt}

\renewcommand{\maketitle}[1]{
  \pagestyle{empty}
  Universität Augsburg\hfill
  Dr.~Felix Cherubini\\
  Lehrstuhl für Algebra und Zahlentheorie\hfill
  Lukas Stoll, M.Sc.\\
  Sommersemester 2021\\
  \begin{center}
    \Large\bfseries
    {#1}.~Übungsblatt zur Homotopietypentheorie
  \end{center}
  \vspace{1.5em}
}

\newcounter{exc}
\newenvironment{exercise}[1][]{
  \addtocounter{exc}{1}\textbf{Aufgabe \theexc.} \emph{#1}\par
}{\vspace{1.5em}}
\newenvironment{bonus}[1][]{
  \textbf{Bonusaufgabe.} \emph{#1}\par
}{\vspace{1.5em}}
