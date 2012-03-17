;;; example setting for Mizar mode

 (global-font-lock-mode t)
 (setq require-final-newline t)
 (setq load-path (cons (substitute-in-file-name "$MIZFILES") load-path))
 (autoload 'mizar-mode "mizar" "Major mode for editing Mizar articles." t)
 (autoload 'mmlquery-decode "mizar")
 (autoload 'mmlquery-mode "mizar")
 (setq auto-mode-alist (append '(  ("\\.miz" . mizar-mode)
                                   ("\\.abs" . mizar-mode))
 			      auto-mode-alist))
 (setq format-alist 
      (append  '(
		 (text/mmlquery "Extended MIME text/mmlquery format." 
		  "::[ \t]*Content-[Tt]ype:[ 	]*text/mmlquery"
		  mmlquery-decode nil nil mmlquery-mode))
	       format-alist))
