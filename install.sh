#!/bin/sh

HEADER_STR="Installation of Mizar System Version 7.7.01 (Linux/FPC) (MML 4.67.942)"
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

   dialog \
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

   dialog \
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
   fi
   
   dialog \
   --title "Shared files installation" \
   --infobox "It may take some time..."  3 60 
   
   cd $INSTALL_MIZ
   gzip -c -d $LDIR/mizshare.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_MIZ"
   cd $LDIR
   
   dialog \
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

   dialog \
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
   echo "Unpacking to $INSTALL_BIN"
   echo " "

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
   echo "Unpacking to $INSTALL_MIZ"
   echo " "

   if [ ! -d $INSTALL_MIZ ] 
    then
     mkdir -p $INSTALL_MIZ || exit_install "Unable to create directory $INSTALL_MIZ"
     chmod a+r $INSTALL_MIZ
    else 
     rm -r -f $INSTALL_MIZ/prel/* || exit_install "Unable to clear directory $INSTALL_MIZ/prel" 
     rm -f $INSTALL_MIZ/abstr/* || exit_install "Unable to clear directory $INSTALL_MIZ/abstr"
     rm -f $INSTALL_MIZ/mml/* || exit_install "Unable to clear directory $INSTALL_MIZ/mml"
   fi

   echo "It may take some time..."
   echo " "

   cd $INSTALL_MIZ
   gzip -c -d $LDIR/mizshare.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_MIZ"
   cd $LDIR

   echo "Enter the path for installing Mizar documentation"
   echo "[default is $INSTALL_DOC]"

   if [ "$DEFAULT" != "yes" ]; then
     read ANS
     if [ "$ANS" != "" ]; then INSTALL_DOC=$ANS; fi
   fi
   echo "Unpacking to $INSTALL_DOC"
   echo " "

   if [ ! -d $INSTALL_DOC ] 
    then
     mkdir -p $INSTALL_DOC || exit_install "Unable to create directory $INSTALL_DOC"
     chmod a+r $INSTALL_DOC
   fi
   
   cd $INSTALL_DOC
   gzip -c -d $LDIR/mizdoc.tar.gz | tar -xf - || exit_install "Error while unpacking to $INSTALL_DOC"
   cd $LDIR

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
  dialog > /dev/null 2>&1
  if [ "$?" != 0 -a ! -x /usr/bin/dialog ]; then start_old_install; else

  dialog \
  --title Info \
  --textbox README 20 70   

  dialog \
  --title Start \
  --yesno "Start the installation ?"  6 30

  case $? in
   0) start_install ;;
   *) exit_install ;;
  esac;
  fi
  ;;
esac
