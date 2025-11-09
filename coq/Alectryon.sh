#!/bin/bash
alectryon -R src/ Fjfj -Q Coquetier/sponge/egg-plugin/theories egg -I Coquetier/sponge/egg-plugin/src  --backend latex --latex-dialect xelatex src/Rf4.v -o alectryon_build/Rf4.tex
alectryon -R src/ Fjfj -Q Coquetier/sponge/egg-plugin/theories egg -I Coquetier/sponge/egg-plugin/src  --backend latex --latex-dialect xelatex src/ChapterEgg.v -o alectryon_build/ChapterEgg.tex
alectryon -R src/ Fjfj -Q Coquetier/sponge/egg-plugin/theories egg -I Coquetier/sponge/egg-plugin/src  --backend latex --latex-dialect xelatex src/coquetier_use.v -o alectryon_build/coquetier_use.tex
alectryon -R src/ Fjfj -Q Coquetier/sponge/egg-plugin/theories egg -I Coquetier/sponge/egg-plugin/src  --backend webpage src/Rf4.v -o alectryon_build/Rf4.html
cd alectryon_build/ 

cat Rf4.tex | sed -e/begin.document./\{ -e:1 -en\;b1 -e\} -ed | sed '1d' | sed '$d' > Rf4_core.tex
cat ChapterEgg.tex | sed -e/begin.document./\{ -e:1 -en\;b1 -e\} -ed | sed '1d' | sed '$d' > ChapterEgg_core.tex
cat coquetier_use.tex | sed -e/begin.document./\{ -e:1 -en\;b1 -e\} -ed | sed '1d' | sed '$d' > coquetier_use_core.tex
#xelatex Rf4.tex