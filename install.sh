#!/bin/sh

HEADER_STR="Installation of Mizar System Version 7.0.02 (Linux/FPC) (MML 4.02.819)"
LDIR=`pwd`
INSTALL_BIN='/usr/local/bin'
INSTALL_DOC='/usr/local/doc/mizar'
INSTALL_MIZ='/usr/local/share/mizar'
INSTALL_TEMP=/tmp/mizar-install-`date +$y%m%d%H%M%S`

exit_install()
 {
  echo "Installation aborted"
  echo "$1"
  if [ -f $INSTALL_TEMP ]; then rm $INSTALL_TEMP; fi
  exit 1
 }

start_install()
 {

   $DIALOG \
   --title Info \
   --textbox README 20 60
   
   $DIALOG \
   --title Executables \
   --inputbox "Enter the path for installing Mizar executables"  10 60 $INSTALL_BIN 2> $INSTALL_TEMP
   if  [ ! -s $INSTALL_TEMP ]; then exit_install; fi
   read INSTALL_BIN < $INSTALL_TEMP
   if [ ! -d $INSTALL_BIN ]; then
     mkdir -p $INSTALL_BIN || exit_install "Unable to create directory $INSTALL_BIN"
     chmod a+r $INSTALL_BIN
   fi
   
   cd $INSTALL_BIN
   gzip -c -d $LDIR/mizbin.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_BIN"
   cd $LDIR

   $DIALOG \
   --title "Shared files" \
   --inputbox "Enter the path for installing Mizar shared files"  10 60 $INSTALL_MIZ 2> $INSTALL_TEMP
   if  [ ! -s $INSTALL_TEMP ]; then exit_install; fi
   read INSTALL_MIZ < $INSTALL_TEMP
   if [ ! -d $INSTALL_MIZ ]
    then
     mkdir -p $INSTALL_MIZ || exit_install "Unable to create directory $INSTALL_MIZ"
     chmod a+r $INSTALL_MIZ
    else
     rm -r -f $INSTALL_MIZ/prel/* || exit_install "Unable to clear directory $INSTALL_MIZ/prel"
     rm -f $INSTALL_MIZ/abstr/* || exit_install "Unable to clear directory $INSTALL_MIZ/abstr"
     rm -f $INSTALL_MIZ/mml/* || exit_install "Unable to clear directory $INSTALL_MIZ/mml"
     rm -f $INSTALL_MIZ/mizar.dct || exit_install "Unable to remove old share files"
     rm -f $INSTALL_MIZ/mizar.dic || exit_install "Unable to remove old share files"
     rm -f $INSTALL_MIZ/mizar.msg || exit_install "Unable to remove old share files"
     rm -f $INSTALL_MIZ/mml.vct || exit_install "Unable to remove old share files"
   fi
   
   $DIALOG \
   --title "Shared files installation" \
   --infobox "It may take some time..."  3 60 
   
   cd $INSTALL_MIZ
   gzip -c -d $LDIR/mizshare.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_MIZ"
   cd $LDIR
   
   $DIALOG \
   --title "Mizar documentation" \
   --inputbox "Enter the path for installing Mizar documentation"  10 60 $INSTALL_DOC 2> $INSTALL_TEMP
   if  [ ! -s $INSTALL_TEMP ]; then exit_install; fi
   read INSTALL_DOC < $INSTALL_TEMP
   if [ ! -d $INSTALL_DOC ] 
    then
     mkdir -p $INSTALL_DOC || exit_install "Unable to create directory $INSTALL_DOC"
     chmod a+r $INSTALL_DOC
   fi
   
   cd $INSTALL_DOC
   gzip -c -d $LDIR/mizdoc.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_DOC"
   cd $LDIR

   $DIALOG \
   --title "Installation completed" \
   --clear \
   --msgbox \
   "\nThe installation process of the Mizar system is completed.\n\n\
Note:\n\n\
The Mizar system requires a variable MIZFILES\n\
which should be set to $INSTALL_MIZ.\n\n\
If $INSTALL_BIN is not in your PATH \n\n\
please add it before running Mizar.\n\n\
With questions or comments contact mus@mizar.uwb.edu.pl" 20 80 ;
   rm $INSTALL_TEMP
 }

start_old_install()
 {
   echo " "
   echo "$HEADER_STR"
   echo " "

   echo "Enter the path for installing Mizar executables"
   echo "[default is $INSTALL_BIN]"

   if [ "$DEFAULT" != "yes" ]; then
     read ANS
     if [ "$ANS" != "" ]; then INSTALL_BIN=$ANS; fi
   fi

   if [ ! -d $INSTALL_BIN ]; then
     mkdir -p $INSTALL_BIN || exit_install "Unable to create directory $INSTALL_BIN"
     chmod a+r $INSTALL_BIN
   fi

   cd $INSTALL_BIN
   gzip -c -d $LDIR/mizbin.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_BIN"
   cd $LDIR

   echo "Enter the path for installing Mizar shared files"
   echo "[default is $INSTALL_MIZ]"

   if [ "$DEFAULT" != "yes" ]; then
     read ANS
     if [ "$ANS" != "" ]; then INSTALL_MIZ=$ANS; fi
   fi

   if [ ! -d $INSTALL_MIZ ] 
    then
     mkdir -p $INSTALL_MIZ || exit_install "Unable to create directory $INSTALL_MIZ"
     chmod a+r $INSTALL_MIZ
    else 
     rm -r -f $INSTALL_MIZ/prel/* || exit_install "Unable to clear directory $INSTALL_MIZ/prel" 
     rm -f $INSTALL_MIZ/abstr/* || exit_install "Unable to clear directory $INSTALL_MIZ/abstr"
     rm -f $INSTALL_MIZ/mml/* || exit_install "Unable to clear directory $INSTALL_MIZ/mml"
     rm -f $INSTALL_MIZ/mizar.dct || exit_install "Unable to remove old share files"
     rm -f $INSTALL_MIZ/mizar.dic || exit_install "Unable to remove old share files"
     rm -f $INSTALL_MIZ/mizar.msg || exit_install "Unable to remove old share files"
     rm -f $INSTALL_MIZ/mml.vct || exit_install "Unable to remove old share files"     
   fi

   echo "It may take some time..."

   cd $INSTALL_MIZ
   gzip -c -d $LDIR/mizshare.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_MIZ"
   cd $LDIR

   echo "Enter the path for installing Mizar documentation"
   echo "[default is $INSTALL_DOC]"

   if [ "$DEFAULT" != "yes" ]; then
     read ANS
     if [ "$ANS" != "" ]; then INSTALL_DOC=$ANS; fi
   fi

   if [ ! -d $INSTALL_DOC ] 
    then
     mkdir -p $INSTALL_DOC || exit_install "Unable to create directory $INSTALL_DOC"
     chmod a+r $INSTALL_DOC
   fi
   
   cd $INSTALL_DOC
   gzip -c -d $LDIR/mizdoc.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_DOC"
   cd $LDIR

   echo " "
   echo "The installation process of the Mizar system is completed."
   echo " "
   echo "Note:"
   echo "The Mizar system requires a variable MIZFILES"
   echo "which should be set to $INSTALL_MIZ."
   echo " "
   echo "If $INSTALL_BIN is not in your PATH please add it before running Mizar."
   echo " "
   echo "With questions or comments contact mus@mizar.uwb.edu.pl"
 }

######################## Proper installation #######################
case $1 in
 '--default') DEFAULT="yes"; start_old_install; exit ;;
 '--nodialog') start_old_install; exit ;;
 *)
  which dialog > /dev/null
  if [ "$?" != 0 ]; then start_old_install; exit; fi
  HEADER_STR=HEAD
  dialog 2>&1 | grep backtitle > /dev/null
  if [ "$?" = 0 ]; then DIALOG="`which dialog` --backtitle $HEADER_STR"; else DIALOG=`which dialog`;fi
  $DIALOG \
  --title Start \
  --yesno "Do yo want to start Mizar installation ?" 6 40
  case $? in
   0) start_install ;;
   *) exit_install ;;
  esac;
  ;;
esac
