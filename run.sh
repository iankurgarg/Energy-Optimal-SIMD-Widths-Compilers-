# run testfilename param 

comp=clang
arrtemp=(${1//./ })
extens=${arrtemp[1]}
testno=${arrtemp[0]} | tail -c 2
if [ "$extens" == "cpp" ]
then
	comp=clang++
fi

cp $1 'test.'$extens
$comp 'test.'$extens -o test
$comp -O0 -emit-llvm 'test.'$extens -c -o test.bc
opt -load ~/sem7/compilers/llvm/Debug+Asserts/lib/PROJECTPASS.so -projectTest <test.bc> /dev/null $2
rm 'test.'$extens test
#rm test
#rm test.bc
