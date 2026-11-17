#!/bin/sh

if [ ! -f oscam.c ]
then
	echo "ERROR: Run this script in the oscam source directory (where oscam.c file is)."
	exit 1
fi

OPTS=$(grep "static const char short_options" oscam.c | sed -e 's|.* \"||;s|\".*||;s|:||g;s|\(.\)|\1 |g')
SOPTS=$(for i in $OPTS; do printf '%s\n' "$i"; done | sort -u)
LOPTS=$(grep "^	{ \"" oscam.c | sed -e 's|.*{ \"||;s|".*||')

printf 'Short options that are free to use:\n    '
for i in A B C D E F G H I J K L M N O P Q R S T U V W X Y Z \
	a b c d e f g h i j k l m n o p q r s t u v w x y z \
	0 1 2 3 4 5 6 7 8 9
do
	if ! printf '%s\n' "$OPTS" | grep -Fq "$i"
	then
		printf '%s' "$i"
	fi
done
printf '\n'

printf "Options that are not processed in oscam.c (missing case 'x'):\n    "
AOPTS="$SOPTS"
for i in $AOPTS
do
	if ! grep -Fq "case '$i'" oscam.c
	then
		printf '%s' "$i"
	fi
done
printf '\n'

printf "Short options that are missing from 'struct long_options[]'\n    "
for i in $AOPTS
do
	if ! grep -Fq "NULL, '$i' }," oscam.c
	then
		printf '%s' "$i"
	fi
done
printf '\n'

printf 'No help entry in usage() for short options:\n    '
for i in $AOPTS
do
	if ! grep -Fq "	printf(\" -$i" oscam.c
	then
		printf '%s' "$i"
	fi
done
printf '\n'

printf 'No help entry in usage() long options:\n'
for i in $LOPTS
do
	if ! grep -q "	printf(\" -., --$i" oscam.c
	then
		printf '    %s\n' "$i"
	fi
done
printf '\n'
