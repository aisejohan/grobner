#! /bin/bash


assign_degrees()
{
	d1=$1
	d2=$2
	d3=$3
	d4=$4
	d=$5
}

change_data()
{
sed -i \
        -e "s@^#define d1\t.*@#define d1\t$d1@" \
        -e "s@^#define d2\t.*@#define d2\t$d2@" \
        -e "s@^#define d3\t.*@#define d3\t$d3@" \
        -e "s@^#define d4\t.*@#define d4\t$d4@" \
        -e "s@^#define d\t.*@#define d\t$d@" data.h
}

while read LINE; do
	echo $LINE | grep -q Special 
	if [ $? = 0 ]; then
		LINE=$(echo $LINE | sed "s/Special: //")
		LINE=$(echo $LINE | sed "s/ and d=/ /")
		LINE=$(echo $LINE | sed "s/, 2.*//")
		assign_degrees $LINE
		REMAINDER=$(($d % $d1))
		if [ ! $REMAINDER = 0 ]; then
			REMAINDER=$(($d % $d2))
			if [ $REMAINDER = 0 ]; then
				TEMP=$d1
				d1=$d2
				d2=$TEMP
			else
				REMAINDER=$(($d % $d3))
				if [ $REMAINDER = 0 ]; then
					TEMP=$d1
					d1=$d3
					d3=$TEMP
				fi
			fi
		fi
		change_data
		sleep 1
		make make_list
		sleep 1
		./tester > outputs/"$d1-$d2-$d3-$d4-$d-p-3"
	fi
done
