python3 gen.py $1 $2;
lake build;
./.lake/build/bin/cyclic_formulas > output.txt;
python3 plot.py $1 $2 < output.txt;
