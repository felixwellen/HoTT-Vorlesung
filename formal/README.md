Wie kommt man an Agda?
======================

Es gibt viele Möglichkeiten, an den Punkt zu kommen, an dem man in Agda loslegen kann.
Die Möglichkeiten unten sind nach aufsteigender Komplexität/Schwierigkeit geordnet.

Agda im Browser ausprobieren
----------------------------
Hier kann man ganz unverfänglich Agda im Browser ausprobieren:

https://agdapad.quasicoherent.io/

(was aber evtl manchmal abgeschaltet ist)

Agda in einer virtuellen Maschine ausprobieren
----------------------------------------------
Dazu gibt es hier ein image, das ich (Felix) nicht getestet habe:
https://agdapad.quasicoherent.io/#__info


Agda als Paket installieren
---------------------------
Viele Linux-Distributionen haben ein Paket für eine (ältere) Version von Agda.
Für den Anfang reicht das sicher aus.
Üblicherweise installieren diese Paket auch einen Emacs-Modus für Agda.
Es könnte sein, dass das auch in der Ubuntu-App für Windows 10 geht.
Ein paar Details zu einzelnen Distros und Mac OS X sind hier:

https://agda.readthedocs.io/en/v2.6.0.1/getting-started/installation.html

Agda komilieren
---------------
Auf den meisten aktuellen System sollte es möglich sein, Agda zu kompilieren.
Der Vorgang braucht typischerweise (auf 64bit-Systemen) mehr als 4G Ram. Wenn man das nicht hat,
sollte man also über andere Optionen nachdenken.

Wichtig ist seit kurzem, dass man auch alle submodules pullt.
Der einfachste Weg meiner (Felix) Erfahrung nach ist, das build-tool 'stack' zu verwenden.
Hier ist eine Anleitung dazu:

https://github.com/agda/cubical/blob/master/INSTALL.md#stack-install-instructions

Hier noch ein paar speziellere:

https://schneide.blog/2019/11/11/compiling-and-using-agda-through-the-windows-linux-subsystem/

https://schneide.blog/2020/09/21/compiling-agda-2-6-2-on-fedora-32/