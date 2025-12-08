#### Failide kirjeldus
Põhiline fail on PR.v. Seal on algne Aksel Õimi tõestus, viimased ~20 rida on ekstraheerimise kohta. Viimasel real on võrgu FN2 ekstraheerimise käsk.
Kaustas push-relabel on projekt, mille bin kaustas main.ml failis on OCaml-i kood, mille saab PR.v ekstraheerimisel.
Lisaks sellele on faili lõpus ka ajamõõtmise ja koodi jooksutamise funktsioonid. Faili alguses on rida, milles ignoreeritakse mõningaid OCaml-i hoiatusi.
Kaustas gen_flow on Pythoni skript graafide genereerimiseks ja hulk graafe, mida testimisel on kasutatud. Selles kaustas on ka varasemate graafide kaust,
kust võib leida need graafid, mille puhul ei ole _backbone_ tee implementatsiooni eemaldatud.

#### OCamli koodi jooksutamine
Kõigepealt tuleb OCaml keskkond käivitada käsuga `ocaml`
Põhikäsk on konsoolis `#use "main.ml";;`
Kui see ei tööta, võib proovida `#use "topfind";;` ja `#require "zarith";;` käske ning seejärel uuesti `#use "main.ml";;`
Kui ikka ei tööta, siis ...
