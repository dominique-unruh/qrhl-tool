while read SESSION; do
    if ! [ -e "$SESSION" ]; then
	if [ -e ../target/downloads/afp/thys/"$SESSION" ]; then
	    echo "Linking $SESSION"
	    ln -s ../target/downloads/afp/thys/"$SESSION" "$SESSION"
	else
	    echo "Could not find $SESSION"
	fi
    fi
done <ROOTS
