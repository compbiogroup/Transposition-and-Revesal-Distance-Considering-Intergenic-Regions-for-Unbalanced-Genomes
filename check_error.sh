pre=$1
suf=$2


for file in `ls $pre/*$suf`; do
        cat $file | grep 'ERROR' | wc -l
done