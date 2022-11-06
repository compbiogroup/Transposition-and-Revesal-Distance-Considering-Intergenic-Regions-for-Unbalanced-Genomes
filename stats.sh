pre=$1
suf=$2


echo "exact"

for file in `ls $pre/*$suf`; do
        echo -e -n $file"\t"
        cat $file  | awk '{print $6}' | grep "1.0000" | wc -l
done

echo "dist"

for file in `ls $pre/*$suf`; do
        echo -e -n $file"\t"
        cat $file | awk '{print $4}' | datamash mean 1 min 1 max 1
done

echo "approx"

for file in `ls $pre/*$suf`; do
        echo -e -n $file"\t"
        cat $file | awk '{print $6}' | datamash mean 1 min 1 max 1
done

echo "time"

for file in `ls $pre/*$suf`; do
        echo -e -n $file"\t"
        cat $file | awk '{print $7}' | datamash mean 1 
done