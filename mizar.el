;;; mizar.el --- mizar.el -- Mizar Mode for Emacs
;;
;; $Revision: 1.144 $
;;
;;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;;; Commentary:
;;
;; Emacs mode for authoring Mizar (www.mizar.org) articles.
;; Run C-h f mizar-mode for overview of commands.
;; Complete info, html, pdf and ps documentation is
;; downloadable from http://kti.ms.mff.cuni.cz/~urban/MizarModeDoc.tar.gz .
;; Browse it at http://ktilinux.ms.mff.cuni.cz/~urban/MizarModeDoc/html .


;;; History:
;; 
;; Started by Bob Beck, beck@cs.UAlberta.CA (beck@alberta) as 
;; a mode for Unix version of Mizar-MSE.
;;
;; Since April 3 2000, rewritten and maintained by 
;; Josef Urban (urban@kti.ms.mff.cuni.cz) for use with Mizar Version >= 6.
;;
;; Go to http://kti.ms.mff.cuni.cz/cgi-bin/viewcvs.cgi/mizarmode/mizar.el
;; to see complete revision history.


;;; Usage
;;
;; If you obtained this with your Mizar distribution, just append
;; the .emacs file enclosed there to your .emacs.
;; Otherwise, the latest version of .emacs is downloadable from
;; http://kti.ms.mff.cuni.cz/cgi-bin/viewcvs.cgi/mizarmode/.emacs .


;;; TODO: 
;;
;; better indentation,

(defvar mizar-emacs
  (if (featurep 'xemacs)
      'xemacs
    (if (featurep 'dos-w32)
	'winemacs
      'gnuemacs))
  "The variant of Emacs we're running.
Valid values are 'gnuemacs,'Xemacs and 'winemacs.")

(eval-when-compile
  (require 'compile)
  (require 'font-lock)
  (require 'imenu)
  (require 'info)
  (require 'shell)
  )

(require 'comint)
(require 'cl)
(require 'easymenu)
(require 'etags)
(require 'hideshow)
(require 'dabbrev)
(require 'executable)
(require 'term)
(require 'imenu)
(if (eq mizar-emacs 'xemacs)
    (require 'speedbar) ;; no NOERROR in xemacs
  (require 'speedbar nil t)) ;;noerror if not present


;;;; variables and customization

(defgroup mizar nil
  "Major mode for authoring Mizar articles"
  :group 'languages)

(defgroup mizar-running nil
  "Running the Mizar utilities"
  :group 'mizar)

(defgroup mizar-indenting nil
  "Indenting in the Mizar mode"
  :group 'mizar)

(defgroup mizar-files nil
  "Files and paths settings in the Mizar mode"
  :group 'mizar)

(defgroup mizar-grep nil
  "Grepping in the Mizar mode"
  :group 'mizar)

(defgroup mizar-faces nil
  "Faces for Mizar keywords"
  :group 'mizar)

(defgroup mizar-constructor-explanations nil
  "Constructor explanations for the Mizar mode"
  :group 'mizar)

(defgroup mizar-mml-query nil
  "Support for MML Query in the Mizar mode"
  :group 'mizar)

(defgroup mizar-proof-advisor nil
  "Mizar Proof Advisor settings"
  :group 'mizar)

(defgroup mizar-skeletons nil
  "Skeleton settings for the Mizar mode"
  :group 'mizar)

(defgroup mizar-speedbar nil
  "Speedbar support for the Mizar mode"
  :group 'mizar)

(defgroup mizar-education nil
  "Options for nonstandard Mizaring used when teaching Mizar"
  :group 'mizar)

(defcustom mizar-newline-indents nil
"*Newline indents."
:type 'boolean
:group 'mizar-indenting)

(defcustom mizar-semicolon-indents nil
"*Semicolon indents."
:type 'boolean
:group 'mizar-indenting)

(defcustom mizar-indent-width 2 
"*Indentation width for Mizar articles."
:type 'integer
:group 'mizar-indenting)

(defcustom mizar-align-labels nil
"*Indenting puts labels at the beginning of lines."
:type 'boolean
:group 'mizar-indenting)

(defcustom mizar-abstracts-use-view t
"*View-mode is used for Mizar abstracts."
:type 'boolean
:group 'mizar)

(defcustom mizar-launch-speedbar nil
"Launch speedbar upon entering mizar-mode for the first time.
Speedbar can be (de)activated later by running the command `speedbar'."
:type 'boolean
:group 'mizar-speedbar)

(defcustom mizar-show-output 4
"*Determines the size of the output window after processing.
Possible values: \"none\", 4, 10, \"all\"."
:type '(choice (const :tag "no output" "none")
	       (const :tag "all output" "all")
	       (const :tag "4 lines" 4)
	       (const :tag "10 lines" 10))
:group 'mizar-running)

(defcustom mizar-goto-error "next"
"*What error to move to after processing.
Possible values are none, first, next, previous."
:type '(choice (const :tag "next error after point" "next")
	       (const :tag "first error in the article" "first")
	       (const :tag "first error before point" "previous")
	       (const :tag "no movement" "none"))
:group 'mizar-running)

(defcustom mizar-verifier "verifier"
"*The default Mizar verifier used to check Mizar articles.
This is used in the `mizar-it' function."
:type 'string
:group 'mizar-running)

(defcustom makeenv "makeenv"
"*Program used for creating the article environment.
This is used in the `mizar-it' function."
:type 'string
:group 'mizar-running)

(defcustom mizar-parallel-options " -j2 -e1 "
"*Options passed to the mizp.pl Mizar parallizer.
This is used in the `mizar-it-parallel' function.
Run mizp.pl --man to get overview of the options."
:type 'string
:group 'mizar-running)

(defcustom mizfiles 
(file-name-as-directory  (substitute-in-file-name "$MIZFILES"))
"The directory where MML is installed."
:type 'string
:group 'mizar-files)

(defcustom mizar-allow-long-lines t 
"*Makes Mizar verifier and other utilities allow lines longer than 80 chars.
This is useful when writing an article, however, you should 
remove long lines before submitting your article to MML."
:type 'boolean
:group 'mizar-running)



(defcustom mizar-quick-run t 
"*Speeds up verifier by not displaying its intermediate output.
Can be toggled from the menu, however the nil value is no
longer supported and may be deprecated (e.g. on Windows)."
:type 'boolean
:group 'mizar-running)

(defcustom mizar-grep-case-sensitive t
"*Tells if MML grepping is case sensitive or not."
:type 'boolean
:group 'mizar-grep
)

(defcustom mizar-sb-in-abstracts t
  "Tells if we use speedbar for Mizar abstracts."
:type 'boolean
:group 'mizar-speedbar)

(defcustom mizar-sb-in-mmlquery t
  "Tells if we use speedbar for MMLQuery abstracts."
:type 'boolean
:group 'mizar-speedbar)

(defcustom mizar-do-expl nil
"*Use constructor explanations.
Put constructor format of 'by' items as properties after verifier run.
The constructor representation can then be displayed 
\(according to the value of `mizar-expl-kind') and queried."
:type 'boolean
:group 'mizar-constructor-explanations)

(defcustom mizar-expl-kind 'sorted
"*Variable controlling the display of constructor representation of formulas.
Has effect iff `mizar-do-expl' is non-nil.
Possible values are now 

'sorted for sorted list of constructors in absolute notation.
'constructors for list of constructors in absolute notation,
'mmlquery behaves as 'sorted, but constructors are inserted
directly into the *mmlquery* input buffer.
The mmlquery interpreter has to be installed for this,
see `mmlquery-program-name'.
'translate for expanded formula in absolute notation,
'raw for the internal Mizar representation,
'xml for xml internal Mizar representation

The values 'xml and 'raw are for debugging only, do
not use them to get constructor explanations."
:type '(choice (const :tag "sorted list of constructors" sorted)
	       (const :tag "unsorted list of constructors" constructor)
	       (const :tag "mmlquery input" mmlquery)
	       (const :tag "translated formula" translate)
	       (const :tag "nontranslated (raw) formula" raw)
	       (const :tag "nontranslated (xml) formula" xml))
:group 'mizar-constructor-explanations)

(defcustom mizar-underline-expls nil
"*If t, the clickable explanation spots in mizar buffer are underlined.
Has effect iff `mizar-do-expl' is non-nil."
:type 'boolean
:group 'mizar-constructor-explanations)

(defcustom byextent 1 
"Size of the clickable constructor explanation region.
`mizar-do-expl' has to be non-nil for this.
When `mizar-underline-expls' is non-nil, it is also underlined."
:type 'integer
:group 'mizar-constructor-explanations)

(defvar merak-url "http://merak.pb.bialystok.pl/cgi-bin/mmlquery/")
(defvar megrez-url "http://megrez.mizar.org/cgi-bin/")

(defcustom query-url merak-url
"*URL for the MMLQuery HTML browser."
:type 'string
:group 'mizar-mml-query)

(defcustom query-text-output nil
"If non-nil, text output is required from MML Query."
:type 'boolean
:group 'mizar-mml-query)

(defcustom mizar-query-browser nil
"*Browser for MML Query, we allow 'w3 or default."
:type 'symbol
:group 'mizar-mml-query)

(defcustom mmlquery-abstracts (concat mizfiles "gab/")
  "*Directory containing the mmlquery abstracts for browsing."
:type 'string
:group 'mizar-files
:group 'mizar-mml-query)

;; (defcustom advisor-url "http://lipa.ms.mff.cuni.cz/cgi-bin/mycgi1.cgi"
;; "*URL for the Mizar Proof Advisor."
;; :type 'string
;; :group 'mizar-proof-advisor)

(defcustom advisor-server "lipa.ms.mff.cuni.cz"
"Server for the Mizar Proof Advisor."
:type 'string
:group 'mizar-proof-advisor)


(defcustom advisor-cgi "/cgi-bin/mycgi1.cgi"
"Path to the advisor CGI script on `advisor-server'."
:type 'string
:group 'mizar-proof-advisor)

(defcustom advisor-limit 30
"*The number of hits you want Mizar Proof Advisor to send you."
:type 'integer
:group 'mizar-proof-advisor)

(defcustom mizar-use-momm nil
"*If t, errors *4 are clickable, trying to get MoMM's hints.
MoMM should be installed for this."
:type 'boolean
:group 'mizar-running)

(defcustom mizar-momm-dir (concat mizfiles "MoMM/")
"*Directory containing the MoMM distribution."
:type 'string
:group 'mizar-files)

(defvar mizar-mode-abbrev-table nil
  "Abbrev table in use in Mizar-mode buffers.")
(define-abbrev-table 'mizar-mode-abbrev-table ())

(defcustom mizar-main-color (face-foreground font-lock-function-name-face)
"*Color used for `mizar-main-keywords'."
:type 'color
:group 'mizar-faces)

(defcustom mizar-block-color (face-foreground font-lock-keyword-face)
"*Color used for `mizar-block-keywords'."
:type 'color
:group 'mizar-faces)

(defcustom mizar-normal-color
  (face-foreground font-lock-variable-name-face)
"*Color used for `mizar-normal-keywords'."
:type 'color
:group 'mizar-faces)

(defcustom mizar-skeleton-color mizar-normal-color
"*Color used for `mizar-skeleton-keywords'."
:type 'color
:group 'mizar-faces)

(defcustom mizar-formula-color
  (if (and (boundp 'font-lock-background-mode)
	   (eq font-lock-background-mode 'dark))
      "LightSkyBlue" "Orchid")
"*Color used for `mizar-formula-keywords'."
:type 'color
:group 'mizar-faces)

(defcustom mizar-environment-keywords 
(list "schemes" "constructors" "definitions" 
      "theorems" "vocabularies" "requirements" "registrations" 
      "notations")
"*Keywords starting mizar environmental items." 
:type '(repeat string)
:group 'mizar-faces)


(defcustom mizar-main-keywords 
(list "theorem" "scheme" "definition" "registration" "notation")
"*Keywords starting main mizar text items." 
:type '(repeat string)
:group 'mizar-faces)

(defcustom mizar-block-keywords
(list "proof" "now" "end" "hereby" "case" "suppose")
"*Keywords for Mizar block starts and ends."
:type '(repeat string)
:group 'mizar-faces)

(defcustom mizar-formula-keywords
(list "for" "ex" "not" "&" "or" "implies" "iff" "st" "holds" "being" "does")
"*Keywords for logical symbols in Mizar formulas."
:type '(repeat string)
:group 'mizar-faces)

(defcustom mizar-skeleton-keywords
(list "assume" "cases"  "given" "hence" "let" "per" "take" "thus")
"*Keywords denoting skeleton proof steps." 
:type '(repeat string)
:group 'mizar-faces)

(defcustom mizar-normal-keywords 
(list
 "and" "antonym" "attr" "as" "be" "begin" "canceled" "cluster" 
 "coherence" "compatibility" "consider" "consistency"  
 "contradiction" "correctness" "def" "deffunc" 
 "defpred" "environ" "equals" "existence"
 "func" "if" "identify" "irreflexivity" 
 "it" "means" "mode" "of"  "otherwise" "over" 
 "pred" "provided" "qua" "reconsider" "redefine" "reflexivity" 
 "reserve" "struct" "such" "synonym" 
 "that" "then" "thesis" "when" "where" "with""is" 
 "associativity" "commutativity" "connectedness" "irreflexivity" 
 "reflexivity" "symmetry" "uniqueness" "transitivity" "idempotence" 
 "asymmetry" "projectivity" "involutiveness")
"*Mizar keywords not mentioned in other place."
:type '(repeat string)
:group 'mizar-faces)

(defvar mizar-mode-syntax-table nil)
(defvar mizar-mode-abbrev-table nil)
(defvar mizar-mode-map nil "Keymap used by mizar mode..")


;; current xemacs has no custom-set-default
(if (fboundp 'custom-set-default)
    (progn
; ;; this gets rid of the "Keep current list of tag tables" message
; ;; when working with two tag tables
      (custom-set-default 'tags-add-tables nil)

; ;; this shows all comment lines when hiding proofs
      (custom-set-default 'hs-hide-comments-when-hiding-all nil)
; ;; this prevents the default value, which is hs-hide-initial-comment-block
      (custom-set-default 'hs-minor-mode-hook nil))
  (custom-set-variables
   '(tags-add-tables nil)
   '(hs-hide-comments-when-hiding-all nil)
   '(hs-minor-mode-hook nil)))

(defun mizar-set-indent-width (to)
"Set indent width to TO."
(interactive)
(setq mizar-indent-width to))

(if mizar-mode-syntax-table
    ()
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\" "_" table)
    (modify-syntax-entry ?: ". 12" table)
    (modify-syntax-entry ?\n ">   " table)
    (modify-syntax-entry ?\^m ">   " table)
    (setq mizar-mode-syntax-table table)))

(define-abbrev-table 'mizar-mode-abbrev-table ())

(defun mizar-mode-variables ()
  "The variables used by mizar-mode."
  (set-syntax-table mizar-mode-syntax-table)
  (setq local-abbrev-table mizar-mode-abbrev-table)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^::::\\|^$\\|" page-delimiter)) ;'::..'
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'paragraph-ignore-fill-prefix)
  (setq paragraph-ignore-fill-prefix t)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'mizar-indent-line)
  (make-local-variable 'comment-start)
  (setq comment-start "::")
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "::+ *")
  (make-local-variable 'comment-column)
  (setq comment-column 48)
  (make-local-variable 'comment-indent-function)
  (setq comment-indent-function 'mizar-comment-indent)
  (setq tags-case-fold-search nil)
;  (set (make-local-variable 'tool-bar-map) mizar-tool-bar-map)
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults
      '(mizar-font-lock-keywords nil nil ((?_ . "w"))))  
  )


(defun mizar-mode-commands (map)
  "Set up some initial key bindings (in the keymap MAP) for
common mizar editing functions."
  (define-key map "\t" 'mizar-indent-line)
  (define-key map ";" 'mizar-semicolon)
  (define-key map "\r" 'mizar-newline))

(if mizar-mode-map
    nil
  (setq mizar-mode-map (make-sparse-keymap))
  (define-key mizar-mode-map  "\C-c\C-m" 'mizar-it)
  (define-key mizar-mode-map  "\C-cj" 'mizar-it-parallel)
  (define-key mizar-mode-map  "\C-cc" 'mizar-compile)
  (define-key mizar-mode-map  "\C-c\C-n" 'mizar-next-error)
  (define-key mizar-mode-map  "\C-c\C-p" 'mizar-previous-error)
  (define-key mizar-mode-map "\C-c\C-e" 'mizar-strip-errors)
  (define-key mizar-mode-map "\C-c\C-d" 'mizar-hide-proofs)
  (define-key mizar-mode-map "\C-cg" 'mizar-grep-abs)
  (define-key mizar-mode-map "\C-c\C-g" 'mizar-grep-full)
  (define-key mizar-mode-map "\C-cb" 'mizar-grep-gab)
  (define-key mizar-mode-map "\C-ci" 'mizar-grep-abs-full-items)
  (define-key mizar-mode-map "\C-c\C-c" 'comment-region)
  (define-key mizar-mode-map "\C-c\C-f" 'mizar-findvoc)
  (define-key mizar-mode-map "\C-c\C-l" 'mizar-listvoc)
  (define-key mizar-mode-map "\C-c\C-t" 'mizar-constr)

  (define-key mizar-mode-map "\C-c\C-h" 'mizar-irrths)
  (define-key mizar-mode-map "\C-c\C-v" 'mizar-irrvoc)
  (define-key mizar-mode-map "\C-c\C-i" 'mizar-relinfer)
  (define-key mizar-mode-map "\C-c\C-o" 'mizar-trivdemo)
  (define-key mizar-mode-map "\C-c\C-s" 'mizar-reliters)
  (define-key mizar-mode-map "\C-c\C-b" 'mizar-chklab)
  (define-key mizar-mode-map "\C-c\C-y" 'mizar-relprem)
  (define-key mizar-mode-map "\C-c\C-a" 'mizar-inacc)
  (define-key mizar-mode-map "\C-c\C-z" 'mizar-make-theorem-summary)
  (define-key mizar-mode-map "\C-c\C-r" 'mizar-make-reserve-summary)
  (define-key mizar-mode-map "\C-cr" 'mizar-occur-refs)
  (define-key mizar-mode-map "\C-ce" 'mizar-show-environ)
  (define-key mizar-mode-map "\C-cs" 'mizar-insert-skeleton)
  (define-key mizar-mode-map "\C-cu" 'mizar-run-all-irr-utils)
  (define-key mizar-mode-map "\M-;"     'mizar-symbol-def)
  (define-key mizar-mode-map "\M-\C-i"     'mizar-ref-complete)
  (define-key mizar-mode-map "\C-c\C-q" 'query-start-entry)
  (if (eq mizar-emacs 'xemacs)
      (progn
	(define-key mizar-mode-map [button3]     'mizar-mouse-symbol-def)
	(define-key mizar-mode-map [(shift button3)]     'mizar-mouse-direct-symbol-def)
	(define-key mizar-mode-map [(shift button1)]     'mizar-mouse-direct-show-ref)
;	(define-key mizar-mode-map [(shift button2)]     'mouse-find-tag-history)
	)
    (define-key mizar-mode-map [mouse-3]     'mizar-mouse-symbol-def)
    (define-key mizar-mode-map [(shift down-mouse-3)]     'mizar-mouse-direct-symbol-def)
    (define-key mizar-mode-map [(shift down-mouse-1)]     'mizar-mouse-direct-show-ref)
;    (define-key mizar-mode-map [(shift down-mouse-2)]     'mouse-find-tag-history)
;    (define-key mizar-mode-map [double-mouse-1]     'mizar-mouse-ref-constrs)
)
  (define-key mizar-mode-map "\M-."     'mizar-show-ref)
  (define-key mizar-mode-map "\C-c."     'mizar-show-ref-constrs)
  (mizar-mode-commands mizar-mode-map))

(defvar mizar-tag-ending ";"
"End of the proper tag name in mizsymbtags and mizreftags.
Used for exact completion.")

(defun miz-complete ()
"Used for exact tag completion."
(interactive )
(if (active-minibuffer-window)
    (progn
      (set-buffer (window-buffer (active-minibuffer-window)))
      (insert mizar-tag-ending)
      (minibuffer-completion-help))))


(define-key minibuffer-local-completion-map ";" 'miz-complete)


;;;;;;;;;;;;;;;;;;;;; utilities ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; destructive!
(defun unique (l1)
  (let ((l1 l1))
  (while l1
      (setq l1 (setcdr l1 (delete (car l1) (cdr l1))))))
  l1)

(defun file-size (fname)
"Size of a file FNAME."
(elt (file-attributes fname) 7))

(defun file-mtime (fname)
"Modification time of a file FNAME."
(elt (file-attributes fname) 5))

(defun test-list1 (test l1)
  "Returns the sublist of L1 consisting of those elements satisfying TEST."
  ;; Loop without recursion probably better than previous
  (let ((l2 ()))
    (while l1
      (if (funcall  test  (car l1))
	  (setq l2 (cons (car l1) l2)))
      (setq l1 (cdr l1)))
    (reverse l2)))

(defun remove-from (pos l1)
"Destructively deletes members from POS on in L1."
(let* ((l2  l1)
       (end (nthcdr (- pos 1) l2)))
  (if (consp end)
      (setcdr  end nil))
  l2))


;; reporting stuff stolen from delphi.el
(defvar mizar-progress-last-reported-point nil
  "The last point at which progress was reported.")

(defun mizar-progress-start ()
  "Initialize progress reporting."
  (setq mizar-progress-last-reported-point nil))

(defun mizar-progress-done (&rest msgs)
  "Finalizes progress reporting; contents of MSGS are output as messages."
  (setq mizar-progress-last-reported-point nil)
  (if (null msgs)
      (message "")
    (apply #'message msgs)))

(defun mizar-step-progress (p desc step-size)
  ;; If enough distance has elapsed since the last reported point, 
  ;; then report the current progress to the user.
  (cond ((null mizar-progress-last-reported-point)
         ;; This is the first progress step.
         (setq mizar-progress-last-reported-point p))

        (;(and mizar-verbose
	 (>= (abs (- p mizar-progress-last-reported-point)) step-size)
         ;; Report the percentage complete.
         (setq mizar-progress-last-reported-point p)
         (message "%s %s ... %d%%"
                  desc (buffer-name) (/ (* 100 p) (point-max))))))

;;;;;;;;;;;;  indentation (pretty poor) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar mizar-label-regexp "\\b[a-zA-Z_'0-9]+:"
  "A regexp matching mizar labels.")

(defun mizar-indent-line ()
  "Indent current line as Mizar code."
  (interactive)
  (let ((indent (mizar-indent-level))
	(pos (- (point-max) (point))) beg)
    (beginning-of-line)
    (setq beg (point))
    (skip-chars-forward " \t")
    (if (and mizar-align-labels (looking-at mizar-label-regexp))
	(let ((lab (match-string 0)))
	  (goto-char (match-end 0))
	  (skip-chars-forward " \t")
	  (delete-region beg (point))
	  (insert lab)
	  (if  ( > indent (length lab))
	      (mizar-indent-to (- indent (length lab)))
	    (insert " ")))
      (if (zerop (- indent (current-column)))
	  nil
	(delete-region beg (point))
	(mizar-indent-to indent)))
					;      (indent-to (+ 3 indent)))
    (if (> (- (point-max) pos) (point))
	(goto-char (- (point-max) pos)))
    ))

(defun mizar-indent-to (indent)
  "Insert a space using INDENT."
  (insert-char 32 indent) )             ; 32 is space...cannot use tabs

(defvar mizar-environment-kw-regexp
  (concat "\\b" (regexp-opt mizar-environment-keywords t) "\\b")
  "Regexp matching environmental keywords.")

(defvar mizar-main-kw-regexp
  (concat "\\b" (regexp-opt mizar-main-keywords t) "\\b")
  "Regexp matching main keywords.")


(defun mizar-indent-level ()
  "Compute mizar indentation level."
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward " \t")
    (cond
     ((looking-at "::::::") 0)		;Large comment starts
     ((looking-at "::") (current-column)) ;Small comment starts
     ((looking-at mizar-main-kw-regexp) 0)
     ((looking-at mizar-environment-kw-regexp) 1)
     ((looking-at "\\b\\(environ\\|reserve\\|begin\\)\\b") 0)
     ((bobp) 0)				;Beginning of buffer
     (t
      (let ((empty t) ind more less res)
	;; See previous indentation
	(cond ((looking-at "end;") (setq less t))
	      ((looking-at 
		"\\b\\(proof\\|now\\|hereby\\|case\\|suppose\\)\\b") 
	       (setq more (match-string 0))))
	;; Find previous noncommented line
	(while empty
	  (forward-line -1)
	  (beginning-of-line)
 	  (cond 
	   ((bobp) (setq empty nil))
	   ((and mizar-align-labels (looking-at mizar-label-regexp))
	    (goto-char (match-end 0))
	    (skip-chars-forward " \t")
	    (setq empty nil))
	   (t 
	    (skip-chars-forward " \t")
	    (if (not (looking-at "\\(::\\|\n\\)"))
 		(setq empty nil)))))
 	(if (bobp)
 	    (setq ind 0)		;Beginning of buffer
	  (setq ind (current-column)))	;Beginning of clause
	;; See its beginning
;	(if (and more (= ind 2) (string-equal more "proof"))
;	    0                           ;proof begins inside theorem
	  ;; Real mizar code
	  (cond ((looking-at "\\b\\(proof\\|now\\|hereby\\|case\\|suppose\\)\\b")
		 (setq res (+ ind mizar-indent-width)))
		((or (looking-at mizar-main-kw-regexp)
		     (looking-at mizar-environment-kw-regexp)
		     (looking-at "\\b\\(reserve\\|begin\\)\\b"))
		 (setq res (+ ind 2)))
 		(t (setq res ind)))
	  (if less (max (- ind mizar-indent-width) 0)
	    res)
	  ))
;)
     )))



(defun mizar-comment-indent ()
  "Compute mizar comment indentation."
  (cond ((looking-at "::::::") 0)
	((looking-at "::::") (mizar-indent-level))
	(t
	 (save-excursion
	   (skip-chars-backward " \t")
	   ;; Insert one space at least, except at left margin.
	   (max (+ (current-column) (if (bolp) 0 1))
		comment-column)))
	))


(defun mizar-indent-buffer ()
  "Indent the entire mizar buffer."
  (interactive )
  ( indent-region (point-min) (point-max) nil))

(defun mizar-newline ()
  "Terminate the current line with a newline and indent the next."
  (interactive "*")
  ;; Remove trailing spaces
  (delete-horizontal-space)
  (newline)
  (mizar-bubble-ref-incremental)
  ;; Indent both the (now) previous and current line first.
  (when mizar-newline-indents
    (save-excursion
      (previous-line 1)
      (mizar-indent-line))
    (mizar-indent-line)))

(defun mizar-semicolon (&optional arg)
  "Indent if `mizar-semicolon-indents' and insert ARG semicolons."
  (interactive "*p")
  (self-insert-command (prefix-numeric-value arg))
  (mizar-bubble-ref-incremental)
  (if mizar-semicolon-indents
    (mizar-indent-line)))


;;;;;;;;;;;;;;;;  end of indentation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;; skeletons ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Special lisp parser "lisppars" is used for this

;;; Howto TEST changes to this:
;; * Run lisppars on all accommodated articles - creates .lsp
;; * cat all .lsp into 00all.lsp - quite big
;; * Try Elisp 'read on all lines of 00all.lsp - e.g.
;;   (while (not (eobp)) (read (current-buffer)) (forward-line))
;;   if OK, lisparse produces only valid lisp expressions
;; * Try calling the rest of functions used for creating 
;;   the skeleton string - see 'mizar-insert-skeleton for them -
;;   ** mainly: mizar-parse-fla:
;;   (while (not (eobp)) 
;;     (mizar-parse-fla (cdr (read (current-buffer)))) (forward-line))
;;   ** then mizar-default-skeleton-items:
;;   (while (not (eobp)) (mizar-default-skeleton-items 
;;    (car (mizar-parse-fla (cdr (read (current-buffer)))))) (forward-line))
;;   ** and finally mizar-skeleton-string:
;;   (while (not (eobp)) (mizar-skeleton-string (mizar-default-skeleton-items 
;;    (car (mizar-parse-fla (cdr (read (current-buffer))))))) (forward-line))
;; * the resulting strings should be valid proof skeletons giving only *4
;;   errors, but I haven't written the script which would actually 
;;   check this so far

;;; TODO:
;; * Have some language for specifying skeleton-creating 
;;   functions, to allow users (and machines) to define their 
;;   own custom skeletons.
;;
;; * Our parsing ends at the level of atomic formulas now, both because 
;;   it is much easier to implement within the current Mizar parser, 
;;   and because it simplifies the pretty printing in Emacs. 
;;   So we should extend it to full parsing eventually.
;; 
;; * Add e.g. definitional expansions, when the full parsing is done.
;; * Handle thesis in cases, when it is not explicit - e.g. correctness
;;   conditions.
;;
;; * When both the macro language and the full parsing is done,
;;   do machine learning of optimal skeletons on MML, and be adaptive.

(defvar mizar-binary-connectives '(iff implies or &))
(defvar mizar-quantifiers '(for ex))
(defvar mizar-logical-constants '(thesis contradiction \?))

(defvar mizar-connectives 
(append mizar-binary-connectives mizar-quantifiers mizar-logical-constants
'(st holds not))
"Symbols for Mizar logical connectives.")
	
(defun parse-fla-with (fla connectives)
  "The connectives CONNECTIVES come from the lowest priority here, i.e. 'iff comes first."
  (if connectives
      (let* (tmp (conn1 (car connectives)) (restconn (cdr connectives))
		 (fla (parse-fla-with fla restconn))
		 (beg (car fla)) (conn (cadr fla)))
	(if (eq conn conn1)
	    (progn 
	      (setq beg (cons conn (list beg))
		    fla (cdr fla))
	      (while (eq conn conn1)
		(setq tmp (parse-fla-with (cdr fla) restconn)
		      beg (append beg (list (car tmp)))
		      fla (cdr tmp)
		      conn (if fla (car fla) nil)))
	      (cons beg fla))
	  fla))
    (get-first-formula fla)))
 
(defun get-first-formula (fla)
"Parse the first quantified, atomic, bracketed or negated FLA into a list.
Return list of the rest unparsed, with added car being the parsed first."
(let ((beg (car fla)))
  (cond 
   ((listp beg) fla)

   ((or (stringp beg) (memq beg mizar-logical-constants))
    (cons (list beg) (cdr fla)))

   ((eq 'not beg)
   (let ((cont (get-first-formula (cdr fla))))
     (cons (list 'not (car cont)) (cdr cont))))

   ((and (eq 'does beg) (eq 'not (cadr fla)))
   (let ((cont (get-first-formula (cddr fla))))
     (cons (list 'does 'not (car cont)) (cdr cont))))

   ((eq 'ex beg)
   (let ((tmp (parse-formula (cdddr fla))))
     (cons (list 'ex (cadr fla) 'st (car tmp)) (cdr tmp))))

   ((eq 'for beg)
   (let (rest (start (list 'for (cadr fla))))
     (if (eq 'st (third fla))
	 (setq fla (parse-formula (cdddr fla))
	       start (nconc start (list 'st (car fla)))
	       rest (cdr fla))
       (setq rest (cddr fla)))
     (if (eq 'holds (car rest))
	 (setq start (nconc start (list 'holds))
	       rest (cdr rest)))
     (setq rest (parse-formula rest))
     (cons (nconc start (list (car rest))) (cdr rest))))

   (t (error "Bad formula: %s" (prin1-to-string fla))))))

(defun parse-formula (fla)
"Return the tree of the longest parsable initial segment of FLA.
The rest is returned as cdr.
The lists arising from having parenthesis must have already been handled here."
(let ((res (get-first-formula fla)))
  (if (cdr res)
      (parse-fla-with res mizar-binary-connectives)
    res)))

(defun mizar-parse-protect-brackets (fla)
"Replace sublists in FLA with parsed sublists beginning with 
'PAR recursively. Exceptions are sublist starting with 'Q, which
denote qualified segments."
(if (or (not (listp fla)) (eq 'Q (car fla))) fla
  (cons 'PAR (parse-formula (mapcar 'mizar-parse-protect-brackets fla)))))
    
(defun mizar-parse-fla (fla)
  "The top-level function for parsing lisppars output."
  (parse-formula (mapcar 'mizar-parse-protect-brackets fla)))

(defun current-line ()
  "Return current line number."
  (+ (count-lines 1 (point))
     (if (= (current-column) 0) 1 0)))

(defun mizar-tmp-being-hack (txt)
  "Replace occurrences of `be' by `being' in the text TXT.

  This is a temporary hack; it won't be needed after the be2being
  fixes to Mizar parser are published."
  (replace-regexp-in-string " +be " " being " txt))

(defun mizar-parse-region-fla (beg end)
"Call the lisppars utility to parse a Mizar formula starting at BEG.
BEG must be a start of a top-level sentence, parsing subformulas or 
definiens formulas is not handled now. 
END is not needed for parsing but for annotating the result
with the position, where the skeleton of its proof should start.
See `mizar-insert-skeleton' for more."
(interactive "r")
(save-excursion
  (goto-char beg)
  (let (fla (bline (current-line)) (bcol (+ 1 (current-column)))
	(lspname (concat (file-name-sans-extension (buffer-file-name))
			 ".lsp" )))
    (mizar-it "lisppars" nil nil t)
    (or (file-readable-p lspname)
	(error "The lisppars utility failed, unknown error!"))
    (with-temp-buffer
	(insert-file-contents lspname)
	(goto-char (point-min))
	(unless (re-search-forward (concat "^((pos " (int-to-string bline) " .*")
				   (point-max) t)
	  (error "No formula starting at line %d" bline))
	;; car is position
	(setq fla (mizar-parse-fla 
		   (cdr (read (mizar-tmp-being-hack (match-string 0)))))))
    (goto-char end)
    (list end (car fla))))) ;; fla is singleton
    
(defun mizar-pp-types (types)
(or (eq 'Q (car types)) 
    (error "Bad qualified segment: %s" (prin1-to-string types)))
(mapconcat 'car (cdr types) ""))

(defun mizar-pp-parsed-fla (fla)
  (if (stringp fla) (concat fla " ")
    (let ((beg (car fla)))
      (cond
       ((stringp beg) beg)
       
       ((eq 'PAR beg)
	(concat "(" (mizar-pp-parsed-fla (cadr fla)) ")"))
       
       ((eq 'Q beg)
	(mizar-pp-types fla))
       
       ((eq 'not beg) 
	(concat "not " (mizar-pp-parsed-fla (cadr fla))))

       ((and (eq 'does beg) (eq 'not (cadr fla))) 
	(concat "does not " (mizar-pp-parsed-fla (caddr fla))))
       
       ((memq beg mizar-logical-constants) (symbol-name beg))
       
       ((memq beg mizar-binary-connectives)
	(mapconcat 'mizar-pp-parsed-fla (cdr fla) 
		   (concat " " (symbol-name beg) " ")))
       
       ((eq 'ex beg)
	(concat "ex " (mizar-pp-types (cadr fla)) "st " 
		(mizar-pp-parsed-fla (fourth fla))))
       
       ((eq 'for beg)
	(let* ((st_occurs (eq 'st (third fla)))
	       (rest (if st_occurs (cddddr fla) (cddr fla))))
	  (concat 
	   "for " (mizar-pp-types (cadr fla))
	   (if st_occurs (concat "st " (mizar-pp-parsed-fla (fourth fla))) " ")
	   (if (eq 'holds (car rest)) 
	       (concat "holds " (mizar-pp-parsed-fla (cadr rest)))
	     (mizar-pp-parsed-fla (car rest))))))
       
       (t (error "Unexpected formula: %s" (prin1-to-string fla)))
       ))))

(defvar  mizar-replace-dupl-spaces-skeletons t)
   
(defun mizar-skelitem-string (item)
 "A string representation of the skeleton item ITEM."
(let ((res (replace-regexp-in-string 
	    " *; *$" ";" (mapconcat 'mizar-pp-parsed-fla item " "))))
  (if mizar-replace-dupl-spaces-skeletons      
      (replace-regexp-in-string "  +" " " res)
    res)))


(defun mizar-skeleton-string (skel)
"Print the proof skeleton for parsed formula FLA into a string.
The skeleton SKEL is a list of of items, each item is a list of either strings 
or lists containing parsed formulas, which are later handed over to 
`mizar-pp-parsed-fla'."
(concat "\nproof\n" 
	(mapconcat 'mizar-skelitem-string skel "\n")
	"\nend;\n"))

(defcustom mizar-skeleton-labels 'serial
"*If not nil, skeleton steps produced by `mizar-insert-skeleton' are labeled.
The labels are created by concatenating the value of 
`mizar-default-label-name' with a label number, which increases throughout
the skeleton from its initial value.
The non nil values of this variable determine the initial default as follows

'serial is used for starting from the last skeleton label number + 1 (default),
'constant-one always starts from 1,
'constant-zero always starts from 0."
:type '(choice (const :tag "no labels" nil)
	       (const :tag "serial" serial)
	       (const :tag "always start from one" constant-one)
	       (const :tag "always start from zero" constant-zero))
:group 'mizar-skeletons)

(defcustom mizar-skeleton-labels-on-newline nil
"*If set, each generated skeleton label starts a new line.
See also `mizar-skeleton-labels' and `mizar-default-label-name'."
:type 'boolean
:group 'mizar-skeletons)

(defcustom mizar-default-label-name "Z"
"*Default name of labels inserted when `mizar-skeleton-labels' is set.
This is appended with a label number."
:type 'string
:group 'mizar-skeletons)

(defvar mizar-next-sk-label 0
"Global var used for numbering skeleton steps.")

(defun mizar-next-sk-label ()
"The next free label usable in proof skeletons."
(let ((res ""))
  (when mizar-skeleton-labels
    (setq res (concat 
	       (if mizar-skeleton-labels-on-newline "
"
		 "")
	       mizar-default-label-name 
	       (int-to-string mizar-next-sk-label) ":"))
    (incf mizar-next-sk-label))
  res))
    
(defun mizar-default-assume-items (fla)
"Create the default assumption skeleton for parsed formula FLA. 
The skeleton is a list of items, each item is a list of either strings 
or lists containing parsed formulas, which are later handed over to
`mizar-pp-parsed-fla'."
(let ((beg (car fla)))
  (cond 
   ((eq '& beg)
    (mapcan 'mizar-default-assume-items (cdr fla)))

   ((eq 'PAR beg)
    (mizar-default-assume-items (cadr fla)))

   ((eq 'ex beg)
    (list (list "given" (cadr fla) "such that")
	  (list (fourth fla) ";")))

   ((eq 'not beg) 
    (let ((negfla (cadr fla)))
    (cond 
     ((eq 'PAR (car negfla))
      (mizar-default-assume-items (list 'not (cadr negfla))))
     ((eq 'not (car negfla))  ;; double negation
      (mizar-default-assume-items (cadr negfla)))
     ((eq 'or (car negfla))
      (mizar-default-assume-items 
       (cons '& (mapcar '(lambda (x) (list 'not x)) (cdr negfla)))))
     ((eq 'implies (car negfla))
      (mizar-default-assume-items 
       (list '& (second negfla) (list 'not (third negfla)))))
     (t (list (list "assume" (mizar-next-sk-label) fla ";"))))))

   (t (list (list "assume" (mizar-next-sk-label) fla ";")))
)))

(defcustom mizar-assume-items-func 'mizar-default-assume-items
"*The function creating assumption skeletons out of a parsed formula.
See `mizar-default-assume-items' for an example.
This function is called for creating assumptions in the function
`mizar-default-skeleton-items'."
:type 'function
:group 'mizar-skeletons)

(defun mizar-being2be (txt)
"Replace \"being\" with \"be\" in TXT."
(replace-regexp-in-string " being " " be " txt))

(defun mizar-skel-generalization (types)
"A list of generalizations corresponding to TYPES."
(or (eq 'Q (car types)) 
    (error "Bad qualified segment: %s" (prin1-to-string types)))
(mapcar '(lambda (x) 
	   (list "let" 
		 (replace-regexp-in-string "^ *, *" "" 
					   (mizar-being2be (car x))) ";"))
	(cdr types)))

(defun mizar-get-type-vars (types)
"Get the string of variables from TYPES."
(or (eq 'Q (car types)) 
    (error "Bad qualified segment: %s" (prin1-to-string types)))
(mapconcat '(lambda (x)
	      (replace-regexp-in-string " +\\(being\\|be\\) .*$" "" (car x)))
	   (cdr types) ""))

(defun mizar-atomic-parsed-fla-p (fla)
"The parsed FLA is atomic - string or string in parenthesis."
(let ((res t))
  (while (and res (listp fla))
    (if (eq 'PAR (car fla))
	(setq fla (cdr fla))
      (if (equal 1 (length fla))
	  (setq fla (car fla))
	(setq res nil))))   ;; neither starts with 'PAR not singleton
  res))

(defun mizar-default-skeleton-items (fla)
"Create the default proof skeleton for parsed formula FLA.
The skeleton is a list of items, each item is a list of either strings 
or lists containing parsed formulas, which are later handed over to 
`mizar-pp-parsed-fla'."
(let ((beg (car fla)))
  (cond 
   ((eq 'PAR beg)   ; ignore paranthesis
    (mizar-default-skeleton-items (cadr fla)))

   ((stringp beg)   ; string must be atomic formula - end of recursion
    (list (list "thus" beg ";")))

   ((memq beg mizar-logical-constants)  ; contradiction or error formula
    (list (list "thus" (symbol-name beg) ";")))

   ((eq '& beg)
;; we have to create subproofs for complicated conjuncts
    (cond 
     ((not (third fla)) 	;; end of or recursion - no wrapping
      (mizar-default-skeleton-items (cadr fla)))
     ((mizar-atomic-parsed-fla-p (cadr fla))	;; "atomic" - no wrapping in proof .. end
      (nconc
       (mizar-default-skeleton-items (cadr fla))
       (mizar-default-skeleton-items (cons '& (cddr fla)))))
     (t				;; otherwise we are wrapping in proof .. end
      (nconc
       (list (list "thus" (cadr fla) ))
       (list (list "proof"))
       (mizar-default-skeleton-items (cadr fla))
       (list (list "end;"))
       (mizar-default-skeleton-items (cons '& (cddr fla)))))))

   ((eq 'or beg)
    (if (not (third fla)) ;; end of or recursion
	(mizar-default-skeleton-items (cadr fla))
      (nconc 
       (funcall mizar-assume-items-func (list 'not (cadr fla)))
       (mizar-default-skeleton-items (cons 'or (cddr fla))))))

   ((eq 'implies beg)
    (nconc
     (funcall mizar-assume-items-func (cadr fla))
     (mizar-default-skeleton-items (third fla))))

   ((eq 'iff beg)
    (nconc 
     (list (list "hereby"))
     (mizar-default-skeleton-items (list 'implies (cadr fla) (third fla)))
     (list (list "end;"))
     (mizar-default-skeleton-items (list 'implies (third fla) (cadr fla)))))

   ((eq 'ex beg)
    (nconc 
     (list (list "consider" (cadr fla) ";"))
     (list (list "take" (mizar-get-type-vars (cadr fla)) ";"))
     (mizar-default-skeleton-items (fourth fla))))
	   
   ((eq 'for beg)
    (nconc (mizar-skel-generalization (cadr fla))
	   (if (eq 'st (third fla))
	       (mizar-default-skeleton-items 
		(list 'implies (fourth fla) 
		      (if (eq 'holds (fifth fla)) (sixth fla) (fifth fla))))
	     (mizar-default-skeleton-items
	      (if (eq 'holds (third fla)) (fourth fla) (third fla))))))
   
   (t (list (list "thus" fla ";")))
   )))

(defcustom mizar-skeleton-items-func 'mizar-default-skeleton-items
"*The function creating proof skeletons out of a parsed formula.
See `mizar-default-skeleton-items' for an example.
This function is called in the interactive function
`mizar-insert-skeleton'."
:type 'function
:group 'mizar-skeletons)

(defun mizar-insert-skeleton (beg end &optional label-number)
"Insert a proof skeleton for the formula starting at BEG after point END.

If `mizar-skeleton-labels' is set, prompt additionally for the
first starting label number LABEL-NUMBER, which should be an
integer.  The labels are then generated using
`mizar-default-label-name'.

For this command to work properly, the lisppars utility needs to
be installed (which probably is the case, since lisppars has been
distributed with Mizar since version 6.4), and the Mizar parser
must be able to access the formula contained within the region
delimited by BEG and END (thus, it must not be within the scope
of a comment).

This command calls `mizar-parse-region-fla' to parse the formula
in the region delimiated by BEG and END.  It then creates the
desired skeleton by first using `mizar-skeleton-items-func', and
then, for pretty printing, by using `mizar-skeleton-string'."
  (interactive "r")
  (or label-number (not mizar-skeleton-labels)
      (progn
	(if (eq mizar-skeleton-labels 'constant-zero) 
	    (setq mizar-next-sk-label 0)
	  (if (eq mizar-skeleton-labels 'constant-one) 
	      (setq mizar-next-sk-label 1)))
	(setq label-number
	      (string-to-number
	       (read-string "First skeleton label: " 
			    (int-to-string mizar-next-sk-label))))))
  (if label-number (setq mizar-next-sk-label label-number))
  (save-excursion
    (let ((skel
	   (mizar-skeleton-string 
	    (funcall mizar-skeleton-items-func
		     (cadr (mizar-parse-region-fla beg end))))))
      ;; remove possible final ';' and adjust end
      (goto-char end)
      (skip-chars-backward "\r\n \t" beg)
      (backward-char)
      (when (search-forward ";" end t)
	(replace-match "")
	(setq end (- end 1)))
      (goto-char end)
      (insert skel)
      (indent-region end (+ end (length skel)) nil))))
	
;;;;;;;;;;;;;;;;;  parsing references ;;;;;;;;;;;;;;;;;;;

(defun mizar-ref-at-point ()
  "Return the reference at the point."
  (save-excursion
    (skip-chars-backward "^ \t\n,;()")
    (if (or (looking-at "\\([^ \t\n:,;]+:def [0-9]+\\)")
	    (looking-at "\\([^ \t\n:,;]+:[0-9]+\\)")
	    (looking-at "\\([^ \t\n:,;]+:sch [0-9]+\\)"))
	(buffer-substring-no-properties (match-beginning 1) (match-end 1))
      (current-word))
    ))



(defvar mizar-ref-table (make-vector 512 0)
  "Global hash table containing explanations of references.
The explanations is the 'expl property of the symbols.
   This is used to speed up `mizar-get-ref-str'")

(defun mizar-get-ref-str (win obj pos)
"Get the string explaining reference REF.
The variable `mizar-ref-table' might be modified by this function."
(if (visit-tags-or-die mizreftags)
(save-excursion
  (set-buffer obj)
  (goto-char pos)
  (let ((ref (mizar-ref-at-point)))
    (if (string-match ":" ref) ;; library reference, caching
	(or (get  (intern-soft ref mizar-ref-table) 'expl)
	    (let ((buf (find-tag-noselect ref))
		  (symb (intern ref mizar-ref-table))
		  (res ""))
	      (set-buffer buf)
	      ;; following regexp has to take care of the MML symbols containing semicolon:
	      ;; ';', [;], \;
	      (setq res (if (looking-at "\\([\n]\\|.\\)+?[^\\];[\t\n\r ]") (match-string 0)
			  ""))
	      ;; previous line may contain e.g. "let z;"
	      (if (string-match ":def " ref) 
		  (progn 
		    (forward-line -1)
		    (looking-at ".*[\n]")
		    (setq res (concat (match-string 0) res))))
	      (put symb 'expl res)
	      res))
      ;; local reference, no caching
      (if (re-search-backward (concat "\\([ \t\n\r:]" ref 
				      "[ \t\n\r]*[{:]\\)\\([\n]\\|.\\)+?[^\\];[\t\n\r ]" )
			      (point-min) t)
	  (let ((res1 (match-string 0)))
	    ;; definition
	    (if (string-match (concat ":" ref ":") res1)
		  (progn
		    (forward-line -1)
		    (looking-at (concat "\\(.*[\n].*\\):" ref ":"))
		    (concat (match-string 1) res1))
	      ;; proved or multiple statements
	      (if (string-match "[ \n\r\t]+\\(proof\\|and\\)[ \n\r\t]" res1)
		  (substring res1 1 (match-beginning 0))
		(substring res1 1))))
	""))))))


(defun mizar-bubble-ref-region (beg end)
"Put bubble help to the references between BEG and END."
(save-buffer-state nil
(save-excursion
  (let ((mod (buffer-modified-p)))
    (goto-char beg)
    (while (re-search-forward "[ \t\n\r,]\\([A-Z0-9_]+:\\(def \\|sch \\|th \\)?[0-9]+\\)" 
			      end t)
      (put-text-property (match-beginning 1) (match-end 1) 
			 'help-echo 'mizar-get-ref-str))
    (goto-char beg)
    (while (re-search-forward "\\([ \n\t]\\(by\\|from\\)[ \n\r\t]\\([^;.]*\\)\\)" end t)
      (put-text-property (match-beginning 3) (match-end 3) 
			 'help-echo 'mizar-get-ref-str))
    (set-buffer-modified-p mod)))))


(defvar mizar-bubble-ref-increment 10
"Extent of lines where refs get incrementally bubble-helped.")

(defun mizar-bubble-ref-incremental ()
"Put bubble help to the references in `mizar-bubble-ref-increment' lines."
(save-excursion
  (let ((pos (point)))
    (forward-line (- mizar-bubble-ref-increment))
    (mizar-bubble-ref-region (point) pos))))
		  

;; ref-completion,should be improved for definitions
(defvar mizar-ref-char-regexp "[A-Za-z0-9:'_]")
(defun mizar-ref-complete ()
"Complete the current reference using dabbrevs from current buffer."
(interactive)
(let ((old-check dabbrev-check-other-buffers)
      (old-regexp dabbrev-abbrev-char-regexp)
      (old-case dabbrev-case-fold-search))


  (unwind-protect
      (progn
	(setq dabbrev-check-other-buffers nil
	      dabbrev-abbrev-char-regexp mizar-ref-char-regexp
	      dabbrev-case-fold-search nil)
;	      dabbrev-abbrev-skip-leading-regexp ".* *")
;;	(fset 'dabbrev--abbrev-at-point
;;	      (symbol-function 'mizar-abbrev-at-point))
	(dabbrev-completion))
    (setq dabbrev-check-other-buffers old-check
	  dabbrev-abbrev-char-regexp old-regexp
	  dabbrev-case-fold-search old-case)
  )))


;;;;;;;;;;; grepping ;;;;;;;;;;;;;;;;;;;;;
;;; we should do some additional checks for winemacs

(defvar mizar-abstr (concat mizfiles "abstr"))
(defvar mizar-mml (concat mizfiles "mml"))
(defcustom mizar-grep-in-mml-order nil
"If non-nil, grepping is attempted in the MML processing order.
This is usually advantageous, because the more basic facts and 
definitions are found first.  The MML processing order is taken
from the file `mizar-mml-lar', and prepended with 
`mizar-mml-prepend'."
:type 'boolean
:group 'mizar-grep)

(defcustom mizar-item-grep-show-lines nil
"*If non-nil `mizar-grep-abs-full-items' shows line info too."
:type 'boolean
:group 'mizar-grep)

(defcustom mizar-mml-lar (concat mizfiles "mml.lar")
"The list of Mizar articles in MML processing order.
This is used e.g. for grepping in the MML order, if the
variable `mizar-grep-in-mml-order' is set."
:type 'string
:group 'mizar-files
:group 'mizar-grep)

(defcustom mizar-mml-prepend (list "hidden" "tarski")
"Additional files prepended to those from `mizar-mml-lar'.
This is used e.g. for grepping if `mizar-grep-in-mml-order' is non-nil."
:type '(repeat string)
:group 'mizar-files
:group 'mizar-grep)

(defun mizar-toggle-grep-case-sens ()
"Toggle the case sensitivity of MML grepping."
(interactive)
(setq mizar-grep-case-sensitive (not mizar-grep-case-sensitive)))

(defvar mizar-mml-order-var-name "MML_GREPPING_LIST"
"Name of the environment variable passed to grep tools.
This variable changes according to what extension we are grepping.
We do this not to mess the process buffer with a long list,
and because shell-expansion is difficult across various shells an OSs.")

(defvar mizar-mml-order-list nil
"Holds list of mml files in mml order, read from `mizar-mml-lar'.
If initialized, also contains the size and modifications time of
`mizar-mml-lar', which are checked before using it.")

(defun mizar-init-mml-order ()
"Initialize `mizar-mml-order-list' if necessary.  Return it."
(when (file-readable-p mizar-mml-lar)
  (let ((nsize (file-size mizar-mml-lar)) (ntime (file-mtime mizar-mml-lar)))
    (if (and mizar-mml-order-list
	     (= nsize (car mizar-mml-order-list))
	     (equal ntime (cadr mizar-mml-order-list)))
	mizar-mml-order-list
      (with-temp-buffer
	(insert-file-contents mizar-mml-lar)
	(goto-char (point-min))
	(setq mizar-mml-order-list 
	      (list nsize ntime (delete "" (split-string (buffer-string) "\n")))))))))

(defun mizar-grep-prepare-flist (ext)
"Return a string of files ending with EXT for grep.
Check if want and can grep in MML order.
Print diagnostic message if we want, but cannot."
(let ((flist (concat " *." ext)))
  (when mizar-grep-in-mml-order
    (if (null (mizar-init-mml-order))
	(message "%s not readable, grepping in alphabetical order" mizar-mml-lar)
      (let ((l1 (append mizar-mml-prepend (third mizar-mml-order-list))))
	(setenv mizar-mml-order-var-name  
		(mapconcat '(lambda (x) (concat x "." ext)) l1 " "))
	(setq flist (if (eq mizar-emacs 'winemacs) 
			(concat "%" mizar-mml-order-var-name "%")
		      (concat "$" mizar-mml-order-var-name))))))
  flist))

(defun mizar-grep-abs (exp)
"Grep MML abstracts for regexp EXP.
Variable `mizar-grep-case-sensitive' controls case sensitivity.
The results are shown and clickable in the Compilation buffer."
  (interactive "sregexp: ")
  (let ((old default-directory) (flist (mizar-grep-prepare-flist "abs")))
    (unwind-protect
	(progn
	  (cd mizar-abstr)
	  (if mizar-grep-case-sensitive
	      (grep (concat "grep -n -E \"" exp "\" " flist))
	    (grep (concat "grep -i -n -E \"" exp "\" " flist))))
      (cd old)
    )))

(defun mizar-grep-full (exp)
"Greps full MML articles for regexp EXP.
Variable `mizar-grep-case-sensitive' controls case sensitivity.
The results are shown and clickable in the Compilation buffer."
  (interactive "sregexp: ")
  (let ((old default-directory) (flist (mizar-grep-prepare-flist "miz")))
    (unwind-protect
	(progn
	  (cd mizar-mml)
	  (if mizar-grep-case-sensitive
	      (grep (concat "grep -n -E \"" exp "\" " flist))
	    (grep (concat "grep -i -n -E \"" exp "\" " flist))))
      (cd old)
      )))


(defun mizar-grep-abs-full-items (exp gab)
"Grep MML abstracts for regexp EXP, using ';' as record separator,
merging each such record into one line, so that .* and .+ regexps
work acroos multiple lines.
If GAB is non-nil, uses the MMLQuery abstracts and '::' as separator
instead.
You need to have perl installed and executable for this.
This gives better results than `mizar-grep-abs', when formulas 
span several lines in abstracts.
Variable `mizar-grep-case-sensitive' controls case sensitivity.
The results are shown in the *Grep Results* buffer.
By default, the file and line information is not put there, 
since the mizar tag browsing function `mizar-show-ref' can be used.
If you want that information, set the variable 
`mizar-item-grep-show-lines'.  Note that in that case, 
compilation minor mode will be used, rebinding some keys to go to
the file positions."
  (interactive "sregexp: \nP")
  (or (executable-find "perl")
      (error "The perl command is not executable on your system!"))
  (let ((script (if mizar-item-grep-show-lines 
		    (if gab mizar-gab-items-grep-command-lines
		      mizar-full-items-grep-command-lines)
		  (if gab mizar-gab-items-grep-command-nolines
		    mizar-full-items-grep-command-nolines)))
	(flist (mizar-grep-prepare-flist (if gab "gab.raw" "abs ")))
	abuffer proc)
    (unless mizar-grep-case-sensitive
      (setq script (replace-regexp-in-string 
		    "placeholder/" "placeholder/i" script)))
    (setq script (replace-regexp-in-string "placeholder" exp script t t))
    (setq script (concat "perl -e " script flist))

    (setq abuffer (get-buffer-create "*Grep Results*"))
    (set-buffer abuffer)
    (cd (if gab mmlquery-abstracts mizar-abstr))
    (erase-buffer)
    (mizar-mode)
    (if mizar-item-grep-show-lines (compilation-minor-mode))
    (insert "cd " default-directory "\n")
    (goto-char (point-min))

    (setq proc (start-process-shell-command "grep" abuffer script))
    (set-process-sentinel proc 'compilation-sentinel)
    (when mizar-item-grep-show-lines 
      (set-process-filter proc 'compilation-filter))

    (display-buffer abuffer)
    ))

(defun mizar-grep-gab-full-items (exp)
  "Search for expression EXP in full-item GAB's."
(interactive "sregexp: ")
(mizar-grep-abs-full-items exp t))

(defvar mizar-full-items-grep-command-nolines
 (concat 
  " '$/=\";\"; " 
  "while ($f=shift) {open(IN,$f);while (<IN>) "
  "{ s/\\n/;;;/g; if(/placeholder/) {s/;;;/\\n/g; s/^\\n+//; print \"\\n\\n$_\"}} "
  "close(IN)}' ")
 "A Perl program for grepping whole items that end with ';'
in Mizar abstracts.  File names and line numbers are not printed.")

(defvar mizar-gab-items-grep-command-nolines
 (concat 
  " '$/=\"::\"; " 
  "while ($f=shift) {open(IN,$f);while (<IN>) "
  "{ s/\\n/;;;/g; if(/placeholder/) {s/;;;/\\n/g; s/\\n*(::)?$//; print \"\\n\\n::$_\"}} "
  "close(IN)}' ")
 "A Perl program for grepping whole items that end with '::'
in MMLQuery abstracts. File names and line numbers are not printed.")

(defvar mizar-full-items-grep-command-lines
 (concat 
  " '$/=\";\"; " 
  "while ($f=shift) {$ln=1;open(IN,$f);while (<IN>) "
  "{$j=tr/\\n//; if(/placeholder/) "
  "{$bef= $`; $add= $bef =~ tr/\\n//; s/^\\n+//; $ln1=$add+$ln; "
  "print \"\\n\\n$f:$ln1:\\n$_\"}; $ln+=$j}; close(IN)}' ")
 "A Perl program for grepping whole items that end with ';'
in Mizar abstracts. File names and line numbers are printed.")

(defvar mizar-gab-items-grep-command-lines
 (concat 
  " '$/=\"::\"; " 
  "while ($f=shift) {$ln=1;open(IN,$f);$f=~ s/gab.raw/gab/; "
  "while (<IN>) {$j=tr/\\n//; if(/placeholder/) "
  "{$bef= $`; $add= $bef =~ tr/\\n//; s/\\n*(::)?$//; $ln1=$add+$ln; "
  "print \"\\n\\n$f:$ln1:\\n::$_\"}; $ln+=$j}; close(IN)}' ")
 "A Perl program for grepping whole items that end with '::'
in MMLQuery abstracts. File names and line numbers are printed.")

(defun mizar-raw-to-gab (start end)
  "Convert a `gab.raw' references to `.gab' in the region delimited by START and END."
(save-excursion
  (goto-char start)
  (while (re-search-forward "\.gab\.raw" end t)
    (replace-match ".gab"))))

(defun mizar-raw-to-gab-all (buf)
"Fix it all in the end in buffer BUF."
(save-excursion
  (set-buffer buf)
  (goto-char (point-min))
  (while (re-search-forward "^[a-zA-Z0-9_]+\.gab\\(\.raw\\)" nil t)
    (replace-match "" nil nil nil 1))))

(defun mizar-gab-compilation-setup ()
  "Set up a new GAB compilation buffer."
  (make-local-variable 'after-change-functions)
  (make-local-variable 'compilation-finish-functions)
  (add-to-list 'after-change-functions 'mizar-raw-to-gab)
  (add-to-list 'compilation-finish-functions 'mizar-raw-to-gab-all)
)

(defun mizar-grep-gab (exp)
"Grep MML Query abstracts for regexp EXP.
Variable `mizar-grep-case-sensitive' controls case sensitivity.
The results are shown and clickable in the Compilation buffer."
  (interactive "sregexp: ")
  (let ((olddir default-directory) (flist (mizar-grep-prepare-flist "gab.raw"))
	(compilation-process-setup-function 'mizar-gab-compilation-setup))
    (unwind-protect
	(progn
	  (cd mmlquery-abstracts)	  
	  (if mizar-grep-case-sensitive
	      (compile (concat "grep -n -E \"" exp "\" " flist))
	    (compile (concat "grep -i -n -E \"" exp "\" " flist))))
      (cd olddir)
    )))

;;;;;;;;;;;;;;; imenu and speedbar handling ;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar mizar-sb-trim-hack
(cond ((fboundp 'trim-words) (list 'trim-words))
      ((fboundp  'speedbar-trim-words-tag-hierarchy)
       (list 'speedbar-trim-words-tag-hierarchy)))
"Hack ensuring proper trimming across various speedbar versions."
)

(defun mizar-setup-imenu-sb ()
"Speedbar and imenu setup for mizar mode."
(progn
  (setq imenu-case-fold-search nil)
  (setq imenu-generic-expression mizar-imenu-expr)
  (if (featurep 'speedbar)
      (progn
	(speedbar-add-supported-extension ".miz")
	(if mizar-sb-in-abstracts
	    (speedbar-add-supported-extension ".abs"))
	(if mizar-sb-in-abstracts
	    (speedbar-add-supported-extension ".gab"))
	(setq speedbar-use-imenu-flag t
	      speedbar-show-unknown-files nil
	      speedbar-special-mode-expansion-list t
	      speedbar-tag-hierarchy-method mizar-sb-trim-hack
	      ;;'(simple-group trim-words)
	      ;;'('speedbar-trim-words-tag-hierarchy 'trim-words)
	      )))))


;; I want the tags in other window, probably some local machinery
;; should be applied instead of a redefinition here
(defun speedbar-tag-find (text token indent)
  "For the tag TEXT in a file TOKEN, go to that position.
INDENT is the current indentation level."
  (let ((file (speedbar-line-directory indent)))
    (speedbar-find-file-in-frame file)
    (save-excursion (speedbar-stealthy-updates))
    ;; Reset the timer with a new timeout when clicking a file
    ;; in case the user was navigating directories, we can cancel
    ;; that other timer.
    (speedbar-set-timer speedbar-update-speed)
    (switch-to-buffer-other-window (current-buffer))
    (goto-char token)
    (run-hooks 'speedbar-visiting-tag-hook)
    ;;(recenter)
    (speedbar-maybee-jump-to-attached-frame)
    ))

;;;;;;;;;;;;  the tags handling starts here ;;;;;;;;;;;;;;;;;;;;;;;;;
;;; xemacs still seems to be unhappy

(put 'mizar-mode 'find-tag-default-function 'mizar-ref-at-point)

(defvar mizsymbtags (concat mizfiles "abstr/symbtags")
  "Symbol tags file.  It is in in the `abstr' directory of $MIZFILES.")
(defvar mizreftags (concat mizfiles "abstr/reftags")
  "References tags file.  It is in the `abstr' directory of $MIZFILES.")

;; nasty to redefine these two, but working; I could not get the local vars machinery right
(defun etags-goto-tag-location (tag-info)
  (let ((startpos (cdr (cdr tag-info)))
	(line (car (cdr tag-info)))
	offset found pat)
	;; Direct file tag.
	(cond (line (goto-line line))
	      (startpos (goto-char startpos))
	      (t (error "BUG in etags.el: bogus direct file tag")))
      (and (eq selective-display t)
	 (looking-at "\^m")
	 (forward-char 1))
    (beginning-of-line)))

(defun etags-tags-completion-table ()
  (let ((table (make-vector 511 0)))
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward	"^\\([^\177\n]+\\)\177.*\n" nil t)
	(intern	  (buffer-substring (match-beginning 1) (match-end 1))
		table)))
      table))

;; redefined to put the default in minibuffer for quick browsing
(defun find-tag-tag (string)
  (let* ((default (funcall (or find-tag-default-function
			       (get major-mode 'find-tag-default-function)
			       'find-tag-default)))
	 (spec (completing-read (if default
				    (format "%s(default %s) " string default)
				  string)
				;; for Emacs 23 tags-complete-tag no longer exists
				(if (fboundp 'tags-complete-tag) 'tags-complete-tag
				  (tags-lazy-completion-table))
				nil nil default nil default)))
    (if (equal spec "")
	(or default (error "There is no default tag"))
      spec)))

(defvar in-mizar-mouse-symbol-def nil
  "Used for `mizar-mouse-symbol-def'.")

(defun mizar-mouse-symbol-def ()
  "\\<mizar-mode-map>\\[mizar-mouse-symbol-def] is bound to this function.
The first click runs `mizar-symbol-def' and the second click shows the symbol's
completions."
  (interactive)
  (if in-mizar-mouse-symbol-def
      (progn (setq in-mizar-mouse-symbol-def nil)
	     (if (active-minibuffer-window)
		 (miz-complete)))
    (mouse-set-point last-input-event)
    (setq in-mizar-mouse-symbol-def t)
    (mizar-symbol-def))
  )

(defun mizar-mouse-direct-symbol-def ()
  "\\<mizar-mode-map>\\[mizar-mouse-direct-symbol-def] is bound to this function.
Goes directly to the first match of the symbol under the mouse click."
  (interactive)
  (mouse-set-point last-input-event)
  (mizar-symbol-def  t))

(defun mizar-mouse-direct-show-ref ()
  "\\<mizar-mode-map>\\[mizar-mouse-direct-show-ref] is bound to this function.
Goes directly to the reference under the mouse click."
  (interactive)
  (mouse-set-point last-input-event)
  (mizar-show-ref  t))

(defun visit-tags-or-die (name)
  (if (file-readable-p name)
      (visit-tags-table name)
    (error "No tags file %s" name)
    nil))

(defun mizar-symbol-def  (&optional nocompletion tag nootherw)
"Find the definition of a symbol at point with completion using file symbtags.
If in *.abs buffer, show its definition in current window, otherwise,
i.e. in *.miz buffer, show it in other window.
In the *Completions* buffer, aside from its normal key bindings,
';' is bound to show all exact matches.
If invoked by right-click (`mizar-mouse-symbol-def'),
second right-click does this too.
NOCOMPLETION goes to the first hit instead.
If TAG is given, search for it instead.
NOOTHERW finds in current window.
File symbtags is included in the Mizar distribution."
  (interactive)
  (if (visit-tags-or-die mizsymbtags)
      (let ((abs (or nootherw (buffer-abstract-p (current-buffer)))))
	(if nocompletion
	    (let ((tag (or tag (mizar-ref-at-point))))
	      (if abs (find-tag  tag)
		(find-tag-other-window tag)))
	  (if abs (call-interactively 'find-tag)
	    (call-interactively 'find-tag-other-window))))))
  

(defun mizar-show-ref (&optional nocompletion)
  "Find the library reference with completion using file reftags.
Show it in its abstract in other window.
Non-nil NOCOMPLETION goes to the first hit without completing.
Library references are theorems, definitions and schemes imported
from other Mizar articles.
File reftags is included in the Mizar distribution."
  (interactive)
  (if (visit-tags-or-die mizreftags)
      (if nocompletion
	  (find-tag-other-window  (mizar-ref-at-point))
	(call-interactively 'find-tag-other-window))))


(defun symbol-apropos ()
  "Displays list of all MML symbols that match a regexp."
  (interactive)
  (if (visit-tags-or-die mizsymbtags)
      (call-interactively 'tags-apropos)))



(defun mouse-find-tag-history ()
"Popup menu with last 20 visited tags and go to selection.
Works properly only for symbols (not references)."
  (interactive)
  (if (visit-tags-or-die mizsymbtags)
      (let* ((allowed (unique (delete nil (copy-alist find-tag-history)) ))
	     (double (mapcar '(lambda (x) (cons x x)) (remove-from 20 allowed)))
	     (backadded (cons (cons "Go to previous" t) double))
	     (menu (list "Visited symbols" (cons "Tags" backadded)))
	     (tag (x-popup-menu t menu)))
	(if (eq tag t) (pop-tag-mark)
	  (if (stringp tag) (find-tag tag))))))



(defun buffer-abstract-p (x)
"Non nil if buffer X is mizar abstract."
(let ((name  (buffer-file-name x)))
  (and (stringp name)
       (string-match "\.abs$" name))))

(defun mizar-current-abstracts ()
"Return list of buffers of mizar abstracts."
(let ((l (buffer-list)) (l1 ()))
  (while l (if (buffer-abstract-p (car l))
	       (setq l1 (cons (car l) l1)))
	 (setq l (cdr l)))
  l1))

(defun mizar-close-all-abstracts ()
"Close all Mizar abstracts.
Useful when you did too much browsing and want to get back to your
editing buffers."
(interactive)
(let* ((l (mizar-current-abstracts)) (i (length l)))
  (mapcar '(lambda (x) (kill-buffer x)) l)
  (message "%d abstracts closed" i)))

(defun mizar-close-some-abstracts ()
"Choose the abstracts you want to close."
(interactive)
(kill-some-buffers  (mizar-current-abstracts)))

(defun mizar-bury-all-abstracts ()
"Bury (put at the end of buffer list) all Mizar abstracts.
Useful when you did too much browsing and want to get back to your
editing buffers."
(interactive)
(let* ((l (mizar-current-abstracts)) (i (length l)))
  (mapcar '(lambda (x) (bury-buffer x)) l)
  (message "%d abstracts buried" i)))


;;;;;;;;;;;;;;;;;; end of tags handling ;;;;;;;;;;;;;;;;;;;;;;;;

(defun mizar-move-to-column (col &optional force)
"Mizar replacement for `move-to-column'.
Avoids tabs in mizar buffers.
Go to column COL, if FORCE, then insert spaces if short."
(if force
    (let ((new (move-to-column col)))
      (if (< new col)
	  (insert-char 32 (- col new)))) ; 32 is space...cannot use tabs
  (move-to-column col)))
		    
;;;;;;;;;;;;;;;;;; errflag              ;;;;;;;;;;;;;;;;;;
;; error format in *.err: Line Column ErrNbr


;; fixed for xemacs leaving "" in the end
(defun buff-to-numtable ()
  (let ((l (delete "" (split-string (buffer-string) "\n"))))
    (mapcar '(lambda (x)
	       (mapcar 'string-to-number (split-string x)))
	    l)
    ))


(defcustom mizar-max-errors-read 1000
"*The maximal number of errors we take care of.
Note that setting this too high may slow down displaying
the errors after the verification."
:type 'integer
:group 'mizar-running)

(defvar mizar-max-errline-length 30
"The maximal length of one line in the error file.")

(defun mizar-max-errfile-size ()
  "The maximum error file size.  It is the product of `mizar-max-errors-read' and `mizar-max-errline-length'."
  (* mizar-max-errors-read mizar-max-errline-length))

(defun mizar-get-errors (aname)
"Return an unsorted table of errors on ANAME or nil."
(save-excursion
  (let ((errors (concat aname ".err")))
    (when (file-readable-p errors)
	(with-temp-buffer           ; sort columns, then lines
	  (insert-file-contents errors nil 0 (mizar-max-errfile-size))
	  (goto-char (point-min))
	  (when (= 0 (forward-line mizar-max-errors-read)) ; deleting
	    (message "Too many errors, reading only first %d of them!"
		     mizar-max-errors-read)
	    (sleep-for 3)
	    (beginning-of-line)
	    (delete-region (point) (point-max)))
	  (buff-to-numtable)
	  )
      ))))

(defun sort-for-errflag (l)
"Sort with L, greater lines first, then by column."
(let ((l (copy-alist l)))
  (sort l '(lambda (x y) (or (> (car x) (car y))
			     (and (= (car x) (car y))
				  (< (cadr x) (cadr y)))))
	)))



(defun mizar-error-flag (aname &optional table)
"Insert error flags into main mizar buffer for ANAME (like errflag).
If `mizar-use-momm' is non-nil, puts the 'pos property into *4 errors too.
If TABLE is not given, get it with `mizar-get-errors'."
(interactive "s")
(let (lline
      (atab (sort-for-errflag (or table (mizar-get-errors aname))))
      (props (list 'mouse-face 'highlight
		   local-map-kword mizar-momm-err-map)))
  (if atab
      (save-excursion
	(setq lline (goto-line (caar atab)))
	(if (or (and (eq mizar-emacs 'xemacs) (not lline))
		(and (not (eq mizar-emacs 'xemacs)) (< 0 lline)))
	    (error "Main buffer and the error file do not agree, run verifier!"))
	(if (< 0 (forward-line))
	    (insert "\n"))
	(let ((cline (caar atab)) srec sline scol snr
	      (currerrln "::>") (cpos 3))
	  (while atab
	    (setq srec (car atab) sline (car srec)
		  scol (- (cadr srec) 1)         ; 0 based in emacs
		  snr (caddr srec) atab (cdr atab))
	    (if (> cline sline)		; start new line ... go back
		(progn
		  (insert currerrln "\n")    ; insert previous result
		  (forward-line (- (- sline cline) 1))
		  (setq currerrln "::>" cpos 3)
		  (setq cline sline)
		  ))
	    (let* ((snrstr (number-to-string snr))
		   (snrl (length snrstr)))
	      (put-text-property 0 snrl 'help-echo 
				 (mizar-get-err-string snrstr) snrstr)
	      (if (and mizar-use-momm (eq snr 4))  ; add momm stuff
		  (progn
		    (add-text-properties 0 1 props snrstr)
		    (put-text-property 0 1 'pos (list sline (cadr srec))
				       snrstr)))
	      (if (> scol cpos)              ; enough space
		  (progn
		    (setq cpos scol)
		    (if (<  (length currerrln) cpos)
			(let ((str (make-string         ; spaces
				    (- cpos (length currerrln)) 32)))
			  (setq currerrln (concat currerrln str))))
		    (setq currerrln (concat currerrln "*" snrstr)))
		(setq currerrln (concat currerrln "," snrstr)))
	      (setq cpos (+ cpos snrl))))
	  (insert currerrln "\n")  ; the first line
	      )))))


(defvar mizar-err-msgs (concat mizfiles "mizar.msg")
  "File with explanations of Mizar error messages.")

(defvar mizar-err-table nil
  "Global hash table containing error explanations.
The explanations is the 'expl property of the symbols.")

(defun mizar-parse-err-msgs ()
  "Parse `mizar-err-msgs' into `mizar-err-table'."
(let* ((lines (with-temp-buffer
		(insert-file-contents mizar-err-msgs)
		(split-string (buffer-string) "[\n]")))
       (table (make-vector (length lines) 0)))
  (while lines
    (if (string-match "^# +\\([0-9]+\\)\\b" (car lines))
      (let ((symb (intern (match-string 1 (car lines)) table)))
	(put symb 'expl (cadr lines))
	(setq lines (cddr lines)))
      (setq lines (cdr lines))))
  (setq mizar-err-table table)))


(defun mizar-get-err-string (err)
  "Return the error message for error ERR (it is a string).
Initializes `mizar-err-table' if not yet initialized."
  (or mizar-err-table (mizar-parse-err-msgs))
  (or (get  (intern-soft err mizar-err-table) 'expl)
      "  ?"))

(defun mizar-getmsgs (errors &optional cformat)
"Return string of error messages for ERRORS.
If CFORMAT, return list of numbered messages for `mizar-compile'."
(save-excursion
  (let ((buf (find-file-noselect  mizar-err-msgs))
	(msgs (if cformat nil ""))
	(prefix (if cformat " *" "::> "))
)
    (set-buffer buf)
    (goto-char (point-min))
    (while errors
      (let* ((s (number-to-string (car errors)))
	     (res  (concat prefix s ": "))
	     msg)
	(if (re-search-forward (concat "^# +" s "\\b") (point-max) t)
	    (let (p)
	      (forward-line 1)
	      (setq p (point))
	      (end-of-line)
	      (setq msg (buffer-substring p (point)))
	      (setq res (concat res  msg "\n")))
	  (setq res (concat res  "  ?" "\n"))
	  (goto-char (point-min)))
	(if cformat
	    (setq msgs (nconc msgs (list (list (car errors) res))))
	    (setq msgs (concat msgs res)))
	(setq errors (cdr errors))))
    msgs)))


(defun mizar-err-codes (aname &optional table)
  "Generate a list of mizar error codes."
  (sort (unique (mapcar 'third (or table (mizar-get-errors aname)))) '<))
  
(defun mizar-addfmsg (aname &optional table)
"Insert error explanations into mizar buffer for ANAME (like addfmsg).
See `mizar-err-codes' for the meaning of TABLE."
(interactive "s")
(save-excursion
  (goto-char (point-max))
  (if (not (bolp)) (insert "\n"))
  (insert (mizar-getmsgs (mizar-err-codes aname table)))))


(defun mizar-do-errors (aname)
"Add err-flags and errmsgs using ANAME.err in current buffer.
Display error number in the mode line and return number of errors."
(save-excursion
  (let ((errors (concat aname ".err")) (error-nr 0))
    (if (and (file-readable-p errors)
	     (< 0 (file-size errors)))
	(let ((table (mizar-get-errors aname)))
	  (setq error-nr (length table))
	  (mizar-error-flag aname table)
	  (mizar-addfmsg aname table)))
    (verifier-mode-line error-nr)
    error-nr)))
  
(defun mizar-comp-addmsgs (atab expl)
"Replace errcodes in ATAB by  explanations from EXPL.
ATAB is reversed."
(let ((msgs "")
      (atab atab))
  (while atab
    (let* ((l1 expl)
	   (currecord (car atab))
	   (ercode (third currecord)))
      (while (not (= ercode (caar l1)))
	(setq l1 (cdr l1)))
      (setq msgs (concat aname ".miz:" (number-to-string (car currecord)) ":"
			 (number-to-string (cadr currecord)) ":"
			 (cadar l1) msgs)))
    (setq atab (cdr atab)))
  msgs))


(defun mizar-compile-errors (aname)
"Return string of errors and explanations for ANAME in compile-like format.
\"\" if no errors."
  (let ((errors (concat aname ".err")))
    (if (and (file-readable-p errors)
	     (< 0 (file-size errors)))
	(let* ((table (mizar-get-errors aname))
	       (atab (sort-for-errflag table))
	       (expl (mizar-getmsgs (mizar-err-codes aname table) t)))
	  (mizar-comp-addmsgs atab expl))
      "")))


;;;;;;;;;;;;;;; end of errflag ;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;; scanning ;;;;;;;;;;;;;;;;;;;;;

(defvar mizar-symbols-regexp "" "String for fontification of symbols.")
(defvar dct-table-date -1 "Date of the dct file.")

(make-variable-buffer-local 'mizar-symbols-regexp)
(make-variable-buffer-local 'dct-table-date)

;; fixed for xemacs leaving "" in the end
(defun buff-to-symblist ()
(let ((l (delete "" (split-string (buffer-string) "\n")))
      res)
  (while l
;    (if (string-match "^.[0-9]+ \\(.*\\)" (car l))
    (if (string-match "^[GKLMORUV][0-9]+ \\(.*\\)" (car l))
	(setq res (cons (match-string 1 (car l)) res)))
    (setq l (cdr l)))
  (nreverse res)))


(defun mizar-get-dct (aname)
"Return the symbols regexp for an article ANAME."
(save-excursion
  (let ((dct (concat aname ".dct")))
    (if (file-readable-p dct)
	(let ((dctdate (cadr (nth 5 (file-attributes dct)))))
	  (if (/= dct-table-date dctdate)
	      (let (tab)
		(with-temp-buffer           ; sort columns, then lines
		  (insert-file-contents dct)
		  (setq tab (buff-to-symblist)))
		(setq dct-table-date dctdate
		      mizar-symbols-regexp (regexp-opt tab))))))
    mizar-symbols-regexp)))

;;;;;;; some cluster hacking (also for MMLQuery) ;;;;;;;;;;;;;;;;;;
;;; this should be improved by outputting the cluster tables after
; analyzer (or having interactive verifier), we now have only clusters
; after accommodation

; cluster-table stuff commented now, ver. 6.2. resigned on
; collecting; leaving it here since two years from now we will
; be collecting again :-)

; (defvar cluster-table nil "table of clusters for the article")
(defvar eclusters nil "Table of existential clusters for the article.")
(defvar fclusters nil "Table of functor clusters for the article.")
(defvar cclusters nil "Table of conditional clusters for the article.")

; (defvar cluster-table-date -1
; "now as constr-table-date, but should be updated more often")
(defvar ecl-table-date -1
"Now as `constr-table-date', but should be updated more often.")

; (make-variable-buffer-local 'cluster-table)
(make-variable-buffer-local 'eclusters)
(make-variable-buffer-local 'fclusters)
(make-variable-buffer-local 'cclusters)
; (make-variable-buffer-local 'cluster-table-date)
(make-variable-buffer-local 'ecl-table-date)

; (defun parse-cluster-table (aname &optional reload)
;   (let ((cluname (concat aname ".clu")))
;     (or (file-readable-p cluname)
; 	(error "File unreadable: %s" cluname))
;     (let ((cludate (cadr (nth 5 (file-attributes cluname)))))
;       (if (or reload (/= cluster-table-date cludate))
; 	  (let (tab)
; 	    (with-temp-buffer
; 	      (insert-file-contents cluname)
; 	      (setq tab
; 		    (vconcat '("")
; 			     (split-string (buffer-string) " ;[\n]"))))
; 	    (setq cluster-table tab
; 		  cluster-table-date cludate))))))


(defun fix-pre-type (str)
"Change G for type to L in STR.
This is now based on a shaky assumption
that any _real_ G (functor) has at least one field."
  (let ((start 0) (res (copy-sequence str)))
    (while  (setq start (string-match "G\\([0-9]+ [;WV]\\)" res start))
      (aset res start 76)
      (setq start (match-end 0)))
    res))


; (defun fix-pre-type (str &optional table)
;   "expand clusters for types using cluster-table, change G for type to L "
;   (let ((table (or table cluster-table))
; 	(lend 0)  start  mtch cl clnr typ (res ""))
;     (while  (string-match "V[0-9]+ V\\([0-9]+\\) \\([MGL]\\)" str lend)
;       (setq start (match-beginning 0)
; 	    mtch (match-string 1 str)
; 	    clnr (string-to-number mtch)
; 	    cl (if (< clnr (length table))
; 		   (aref table (string-to-number mtch))
; 		 (concat "c" mtch))
; 	    typ (match-string 2 str)
; 	    res (concat res (substring str lend start) cl " "
; 			(if (equal typ "G") "L" typ))
; 	    lend (match-end 0)))
;     (concat res (substring str lend))))


; (defun expand-incluster (str &optional table)
;   "expand cluster entry in .ecl using cluster-table"
;   (let ((table (or table cluster-table)))
;     (string-match "^.[AW][0-9]+" str)
;     (let* ((clnr (string-to-number (substring str 2 (match-end 0))))
; 	   (cl (concat (aref table clnr) ":"))
; 	   (result (replace-match cl t t str)))
;       (if (string-match "C\\([0-9]+\\)[ \t]*$" result)
; 	  (let* ((clnr2 (string-to-number
; 			 (substring result (match-beginning 1)
; 				    (match-end 1))))
; 		 (cl2 (concat ":" (aref table clnr2) )))
; 	    (replace-match cl2 t t result))
; 	result))))


(defun parse-clusters (aname &optional reload)
"Parse the eclusters, fcluster and cclusters tables  for ANAME.
Usually from .ecl file.  Cluster-table must be loaded.
RELOAD does this unconditionally."
(let ((ecldate (cadr (nth 5 (file-attributes (concat aname ".ecl"))))))
  (if (or reload (/= ecl-table-date ecldate))
      (let (ex func cond)  ; (table cluster-table))
	(with-temp-buffer
	  (insert-file-contents (concat aname ".ecl"))
	  (let ((all (split-string (buffer-string) "[\n]")))
	    (while (eq (aref (car all) 0) 143) ; char 143 is exist code
	      (setq ex (cons (car all) ex))
	      (setq all (cdr all)))
	    (while (eq (aref (car all) 0) 102) ; char 102 is 'f'
	      (setq func (cons (car all) func))
	      (setq all (cdr all)))
	    (while (eq (aref (car all) 0) 45) ; char 45 is '-'
	      (setq cond (cons (car all) cond))
	      (setq all (cdr all)))))
	(setq eclusters (vconcat (nreverse ex))
	      fclusters (vconcat (nreverse func))
	      cclusters (vconcat (nreverse cond))
	      ecl-table-date ecldate)
	))))

(defun print-vec1 (vec &optional translate)
"Print vector of strings VEC into string.
Used only for clusters.  Calls `frmrepr' if TRANSLATE."
(let ((res "")
      (l (length vec))
      (i 0))
  (while (< i l)
    (setq res (concat res "\n"
		      (if translate (frmrepr (aref vec i)) (aref vec i))))
    (setq i (+ 1 i)))
  res))
  
  
(defun show-clusters (&optional translate)
"Show the cluster tables in buffer *Clusters*.
Previous contents of that buffer are killed first.
TRANSLATE causes `frmrepr' to be called."
  (interactive)
  ;; This puts a description of bindings in a buffer called *Help*.
  (let ((result (concat (print-vec1 eclusters translate) "\n"
			(print-vec1 fclusters translate) "\n"
			(print-vec1 cclusters translate) "\n")))
		       
    (with-output-to-temp-buffer "*Clusters*"
      (save-excursion
	(set-buffer standard-output)
	(erase-buffer)
	(insert result))
      (goto-char (point-min)))))

; should be tested for 6.2.!
(defun parse-show-cluster (&optional translate fname reload)
  (interactive)
  (save-excursion
    (let ((name (or fname
		    (substring (buffer-file-name) 0
			       (string-match "\\.miz$"
					     (buffer-file-name))))))
					;  (parse-cluster-table name reload)
      (parse-clusters name reload)
      (if translate (get-sgl-table name))
      (show-clusters translate))))


;;;;;;;;;;;;;;; translation for MML Query ;;;;;;;;;;;;;;;;;;;;;;
;; should be improved but mostly works
(defvar constrstring "KRVMLGU")
(defvar cstrlen (length constrstring))
; (defvar constructors '("K" "R" "V" "M" "L" "G" "U"))
(defvar ckinds ["func" "pred" "attr" "mode" "struct" "aggr" "sel"])
(defvar cstrnames [])
(defvar cstrnrs [])
(defvar impnr 0)
(defvar constr-table-date -1
"Set to last accommodation date, after creating the table.
Used to keep tables up-to-date.")

(make-variable-buffer-local 'cstrnames)
(make-variable-buffer-local 'cstrnrs)
(make-variable-buffer-local 'impnr)
(make-variable-buffer-local 'constr-table-date)

(defun cstr-idx (kind)  ; just a position
"Return nil if KIND not in `constrstring', otherwise its position."
(let ((res 0))
  (while (and (< res cstrlen) (/= kind (aref constrstring res)))
    (setq res (+ res 1)))
  (if (< res cstrlen)
      res)))
	      
; (position kind constructors :test 'equal))

(defun make-one-tvect (numvect)
  "Split the string NUMVECT and create a vector of numbers corresponding to the split pieces."
  (vconcat (mapcar 'string-to-int (split-string numvect))))

(defun get-sgl-table (aname)
  "Two vectors created from the .sgl file for ANAME."
  (let ((sglname (concat aname ".sgl")))
    (or (file-readable-p sglname)
	(error "File unreadable: %s" sglname))
    (let ((sgldate (cadr (nth 5 (file-attributes sglname)))))
      (if (/= constr-table-date sgldate)
	  (let* ((decl (with-temp-buffer
			 (insert-file-contents sglname)
			 (split-string (buffer-string) "[\n]")))
		 (count (string-to-number (car decl)))
		 (result (cdr decl))
		 (tail (nthcdr count decl))
		 (nums (cdr tail))
		 names)
	    (setcdr tail nil)
	    (setq names (vconcat result (list (upcase aname))))
	    (setq nums (vconcat (mapcar 'make-one-tvect nums)))
	    (list names nums)
	    (setq impnr (- (length names) 1)
		  cstrnames names
		  cstrnrs nums
		  constr-table-date sgldate)
	    )))))

(defun idxrepr (idx nr)
"Does the work for tokenrepr, IDX is index of constrkind.  NR bounds the indices of the array references considered."
  (let ((artnr 0))
    (while (and (< artnr impnr)
		(< (aref (aref cstrnrs artnr) idx) nr))
      (setq artnr (+ artnr 1)))
    (if (or (< artnr impnr)
	    (<= nr (aref (aref cstrnrs artnr) idx)))
	(setq artnr (- artnr 1)))
    (concat (aref cstrnames artnr) ":"
	    (aref ckinds idx) "."
	    (int-to-string (- nr (aref (aref cstrnrs artnr) idx))))
    ))

(defun tokenrepr (kind nr)
"Return absolute name of a lexem KIND, NR, if possible.
Uses the global tables `cstrnames' and `cstrnrs'."
  (let ((idx (cstr-idx kind))
	(artnr 0))
    (if idx (idxrepr idx nr)
      (concat kind (int-to-string nr))
      )))

;;; ###REMOVE after debugging - replaced by xml
(defvar mizartoken2human
  (let ((table (make-vector 256 0))
	(i 0))
    (while (< i 256) (aset table i (char-to-string i)) (incf i))
    (aset table 38 "and ")
    (aset table 170 "not ")
    (aset table 157 "for ")
    (aset table 144 "is ")
    (aset table 37 "verum ")
    (aset table 63 "unknown ")
    table)
"Table translating internal tokens for formula kinds.")

(defun mizar-typ-repr (typ)
"Relative repr of a xml type TYP."
(let ((head (car typ)) (atts (cadr typ)) (args (cddr typ)))
(if (equal (car args) "") (setq args nil))
(cond
 ((eq head 'Typ)
  (let ((knd (xml-get-attribute typ 'kind)))
    (if (equal knd "G") (setq knd "L"))  ;; fixing clash with aggregates
    (if (equal knd "errortyp") knd
      (let ((res (concat knd (xml-get-attribute typ 'nr)))
	    (adjs (cddr (cadr args))) ;; omit lower cluster
	    (adjstr ""))
	(if (equal (car adjs) "") (setq adjs nil))
	(while adjs
	  (let ((non (if (equal "false" 
				(xml-get-attribute (car adjs) 'value))
			 "non " ""))
		(at (concat "V" (xml-get-attribute (car adjs) 'nr)))
		(ar1 (if (and (cddr (car adjs)) 
			      (not (equal "" (car (cddr (car adjs)))))) 
			 (concat "( " (mapconcat 'mizar-term-repr
						(cddr (car adjs)) ", ") " )" )
		       "")))
	    (setq adjstr (concat adjstr " " non at ar1)
		  adjs (cdr adjs))))
	(setq args (cddr args))
	(concat adjstr " " res
		(if args (concat "( " 
				 (mapconcat 'mizar-term-repr args ", ") " )")
		  ""))))))
 (t (error "Unexpected Mizar typ: %s" (symbol-name head))))))
	
(defun mizar-term-repr (trm)
"Relative repr of a xml term TRM."
(let ((head (car trm)) (atts (cadr trm)) (args (cddr trm)))  
(if (equal (car args) "") (setq args nil))
(cond
 ((eq head 'Func)
  (concat (xml-get-attribute trm 'kind)
	  (xml-get-attribute trm 'nr) "( " 
	  (mapconcat 'mizar-term-repr args ", ") " )" ))
 ((eq head 'PrivFunc)
  (concat "privfunc" (xml-get-attribute trm 'nr) "( " 
	  (mapconcat 'mizar-term-repr (cdr args) ", ") " )" ))
 ((eq head 'Var) (concat "B" (xml-get-attribute trm 'nr)))
 ((eq head 'LocusVar) (concat "A" (xml-get-attribute trm 'nr)))
 ((eq head 'Const) (concat "C" (xml-get-attribute trm 'nr)))
 ((eq head 'Num) (xml-get-attribute trm 'nr))
 ((eq head 'It) "it")
 ((eq head 'ErrorTrm) "error")
 ((eq head 'Fraenkel)
  (let ((res "") (lbound mizar-boundnr))
    (while (eq (caar args) 'Typ)
      (let ((tmp (concat "B" (int-to-string (incf mizar-boundnr))
			 " is " (mizar-typ-repr (car args)))))
	(setq res (if (equal res "") tmp (concat res ", " tmp)))
	(setq args (cdr args))))
    (setq res (concat "{ " (mizar-term-repr (car args)) " " res ":"
		      (mizar-frm-repr (cadr args)) " }")
	  mizar-boundnr lbound)
    res))
 (t (error "Unexpected Mizar term: %s" (symbol-name head))))))

(defun proper-list-p (object)
  "Determine whether OBJECT is a proper list."
  (labels ((proper (current slow)
             (cond ((null current)       t)
                   ((atom current)       nil)
                   ((null (cdr current)) t)
                   ((atom (cdr current)) nil)
                   ((eq current slow)    nil)
                   (t                    (proper (cddr current) (cdr slow))))))
    (proper object (cons nil object))))

(defun delete-tree (elt seq)
  "Delete element ELT from the sequence SEQ, regarded as a tree."
  (if (atom seq)
      (if (equal seq elt)
	  nil
	seq)
    (if (proper-list-p seq)
	(let ((trimmed (delete elt seq)))
	  (mapcar #'(lambda (s) (delete-tree elt s)) trimmed))
      seq)))

      
(defun mizar-frm-repr (frm &optional cstronly)
  "Relative repr of a xml formula FRM."
  (let ((head (car frm)) 
	(atts (cadr frm))
	(args (cddr frm)))
    (if (equal (car args) "") (setq args nil))
    (cond
     ((eq head 'Pred)
      (concat (xml-get-attribute frm 'kind)
	      (xml-get-attribute frm 'nr) "( " 
	      (mapconcat 'mizar-term-repr args ", ") " )" ))
     ((eq head 'PrivPred)
      (concat "privpred" (xml-get-attribute frm 'nr) "( " 
	      (mapconcat 'mizar-term-repr (butlast args) ", ") " )" ))
     ((eq head 'Not)
      (concat "not " (mizar-frm-repr (car args)) ))
     ((eq head 'Verum) "verum")
     ((eq head 'ErrorFrm) "error")
     ((eq head 'And) 
      (concat "( " (mapconcat 'mizar-frm-repr args " & ") " )" ))
     ((eq head 'For) 
      (let ((res
	     (concat "for B" (int-to-string (incf mizar-boundnr)) " being"
		     (mizar-typ-repr (car args)) " holds "
		     (mizar-frm-repr (cadr args)))))
	(decf mizar-boundnr)
	res))
     ((eq head 'Is) 
      (concat (mizar-term-repr (car args)) " is "
	      (mizar-typ-repr (cadr args))))
     (t (error "Unexpected Mizar formula: %s" (symbol-name head))))))

(defun frmrepr (prop)
  "Relative repr of a formula in the xml proposition PROP."
  (or (require 'xml nil t) 
      (error "Your Emacs lacks the xml parsing library, please upgrade"))
  (setq mizar-boundnr 0)
  (let ((parsed (with-temp-buffer
		  (insert prop)
		  (goto-char (point-min))
		  (while (search-forward "\n" (point-max) t)
                          (replace-match ""))
		  (xml-parse-region (point-min) (point-max)))))
    (let ((trimmed (delete-tree "\n" parsed)))
      (mizar-frm-repr (car (cddr (car trimmed))) cstronly))))

(defun frmrepr-abs (frm &optional cstronly)
"Absolute repr of a formula FRM.
If CSTRONLY, only list of constructors,
The clusters inside FRM must already be expanded here."
  (let* ((frm1 frm) (res (if cstronly nil ""))
	(cur 0) (end (or (position 39 frm1) (length frm1)))) ;
    (while (< cur end)
      (let* ((tok (aref frm1 cur))
	     (nonv (= tok 87))   ; W
	     (idx (if nonv (cstr-idx 86) ; V - we put the "non" back below
		    (cstr-idx tok))))
	(if idx
	    (let* ((cur1 (+ cur 1))
		   (nr1 "") (cont t) n1)
	      (while (and cont (< cur1 end)) ;number
		(setq n1 (aref frm1 cur1))
		(if (and (< 47 n1) (< n1 58))
		    (setq nr1 (concat nr1 (char-to-string n1))
			  cur1 (+ cur1 1))
		  (setq cont nil)))
	      (setq tok (idxrepr idx (string-to-number nr1))
		    cur cur1)
	      (setq res
		    (if cstronly (nconc res (list tok))
		      (concat res (if nonv "non " "") tok))))
	  (setq cur (+ 1 cur))
	  (if (not cstronly)
	      (setq res (concat res ;;(aref mizartoken2human tok)
				(char-to-string tok)))))))
    res))

(defun expfrmrepr (prop &optional cstronly)
  (frmrepr-abs (frmrepr prop) cstronly))

(defun mizar-getbys (aname)
  "Get constructor repr of propositions from the .xml file for ANAME."
  (let ((prename (concat aname ".xml")))
    (or (file-readable-p prename)
	(error "File unreadable: %s" prename))
    (let (res)
      (with-temp-buffer
	(insert-file-contents prename)
	(goto-char (point-min))
	(while (re-search-forward
		"<Proposition line=.\\([0-9]+\\). col=.\\([0-9]+\\).[^>]*>\\(.\\|[\n]\\)+?<\/Proposition>"
		(point-max) t)
	  (let ((line (match-string 1))
		(col (match-string 2))
		(frm (match-string 0)))
	    (setq res (cons (list (string-to-number line)
				  (string-to-number col) frm) res)))))
      (nreverse res))))

;; kill after debugging, old pre-xml version
(defun mizar-getbys-old (aname)
  "Get constructor repr of bys from the .xml file for ANAME."
  (let ((prename (concat aname ".xml")))
    (or (file-readable-p prename)
	(error "File unreadable: %s" prename))
    (let (res)
      (with-temp-buffer
	(insert-file-contents prename)
	(goto-char (point-min))
	(while (re-search-forward
		"e[0-9]+ [0-9]+ [0-9]+ \\(.*\\)['][^;]*; *\\([0-9]+\\) \\([0-9]+\\)"
		(point-max) t)
	  (let ((line (match-string 2))
		(col (match-string 3))
		(frm (match-string 1)))
	    (setq res (cons (list (string-to-number line)
				  (string-to-number col) frm) res)))))
      (nreverse res))))
      

(defvar mizar-expl-map
  (let ((map (make-sparse-keymap))
	(button_kword (if (eq mizar-emacs 'xemacs) [(shift button3)]
			[(shift mouse-3)])))
    (set-keymap-parent map mizar-mode-map)
    (define-key map button_kword 'mizar-show-constrs-other-window)
    (define-key map "\M-;"     'mizar-show-constrs-kbd)
    map)
"Keymap used at explanation points.")

(defconst local-map-kword
  (if (eq mizar-emacs 'xemacs) 'keymap 'local-map)
  "Xemacs vs.  Emacs local-map.")

(defun mizar-put-bys (aname)
"Put the constructor representation of bys as text properties
into the mizar buffer ANAME.  Underlines and mouse-highlights the
places."
(save-excursion
; check at least for the .xml file, not to exit with error below
(if (not (file-readable-p (concat aname ".xml")))
    (message "Cannot explain constructors, verifying was incomplete")
  (get-sgl-table aname)
;  (parse-cluster-table aname)
  (let ((bys (mizar-getbys aname))
	(oldhook after-change-functions)
	(map mizar-expl-map)
	(help (substitute-command-keys
	       "\\<mizar-expl-map>\\[mizar-show-constrs-other-window] or \\<mizar-expl-map>\\[mizar-show-constrs-kbd]: display constructor representation"))
	props)
    (setq after-change-functions nil)
    (setq props (list 'mouse-face 'highlight local-map-kword map
		      'help-echo help))
    (if mizar-underline-expls
	(setq props (append props '(face underline))))
    (while bys
      (let* ((rec (car bys))
	     (line (car rec))
	     (col (cadr rec))
	     (frm (third rec))
	     beg eol end)
	(goto-line line)
	(end-of-line)
	(setq eol (point))
	(move-to-column col)
	(setq beg (point)
	      end (min eol (+ byextent beg)))
	(add-text-properties beg end props)
	(put-text-property beg end 'cexpl frm)
	(setq bys (cdr bys))))
    (setq after-change-functions oldhook)
    nil))))

(defun mizar-underline-cexpls (start)
"Add 'underline to 'cexp.
Only if `mizar-underlines-expls' is non-nil."
(if mizar-underline-expls
    (save-buffer-state 
     nil
     (save-excursion
       (goto-char start)
       (while (not (eobp))
	 (let ((mfprop (get-text-property (point) 'cexpl))
	       (next-change
		(or (next-single-property-change (point) 'cexpl
						 (current-buffer))
		    (point-max))))
	   (if mfprop
	       (put-text-property (point) next-change 'face 'underline))
;	       (let ((face (get-text-property (point) 'face)))
;		 (setq face (mmlquery-underlined-face face))
;		 (put-text-property (point) next-change 'face face);'(:underline "red");'underline
;;))
	   (goto-char next-change)))))))

(defun mizar-underline-in-region (beg end)
  (mizar-underline-cexpls beg))


(defvar res-regexp "\\([A-Z0-9_]+\\):\\([a-z]+\\)\\([.]\\)\\([0-9]+\\)"
"Description of the mmlquery resource format we use, see idxrepr.")

(defvar mizar-cstr-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-m" 'mizar-kbd-res-mmlquery)
    (define-key map "\C-\M-m" 'mizar-kbd-ask-query)
    (define-key map "\M-." 'mizar-kbd-cstr-tag)
    (define-key map "\C-c\C-c" 'mizar-ask-advisor)
    (if (eq mizar-emacs 'xemacs)
	(progn
	  (define-key map [button2] ' mizar-mouse-res-mmlquery)
	  (define-key map [(shift button2)] 'mizar-mouse-ask-query)
	  (define-key map [button3] 'mizar-mouse-cstr-tag))
      (define-key map [mouse-2] 'mizar-mouse-res-mmlquery)
      (define-key map [(shift mouse-2)] 'mizar-mouse-ask-query)
      (define-key map [mouse-3] 'mizar-mouse-cstr-tag))
    map)
"Keymap in the buffer *Constructors list*.
Used for viewing constructor meanings via symbtags or sending
constructor queries to MML Query.
Commands:
\\{mizar-cstr-map}")

; Xemacs vs. Emacs
(if (not (fboundp 'event-window))
    (fset 'event-window (lambda (e) (posn-window (event-end e)))))
(if (not (fboundp 'event-point))
    (fset 'event-point (lambda (e) (posn-point (event-end e)))))

(defun mizar-ask-query (query)
  "Open a browser and ask query QUERY."
  (if (eq mizar-query-browser 'w3)
      (browse-url-w3 query)
    (browse-url query)))

(defun mizar-ask-meaning-query (cstr)
"Send a constructor query CSTR to MML Query."
(interactive "s")
(mizar-ask-query (concat query-url "meaning?entry=" cstr)))

(defun mizar-res-at-point (pos &optional agg2str)
"Get the mmlquery resource around POS.  If AGG2STR is non-nil,
replace aggr by struct."
(save-excursion
  (goto-char pos)
  (skip-chars-backward ":.a-zA-Z_0-9")
  (if (looking-at res-regexp)
      (let ((res (match-string 0)))
	(if (and agg2str (equal "aggr" (match-string 2)))
	    (concat (match-string 1) ":struct." (match-string 4))
	  res)))))

(defun mizar-mouse-ask-query (event)
"Ask MML Query about the mmlquery resource we clicked on."
  (interactive "e")
  (select-window (event-window event))
  (let ((cstr (mizar-res-at-point (event-point event))))
    (if cstr (mizar-ask-meaning-query cstr)
      (message "No mmlquery resource at point"))))

(defun mizar-kbd-ask-query (pos)
"Ask MML Query about the mmlquery resource at position POS."
  (interactive "d")
  (let ((cstr (mizar-res-at-point pos)))
    (if cstr (mizar-ask-meaning-query cstr)
      (message "No mmlquery resource at point"))))


(defun mizar-mouse-res-mmlquery (event)
"Find the definition of the mmlquery resource we clicked on in its
MMLQuery abstract."
  (interactive "e")
  (select-window (event-window event))
  (let ((cstr (mizar-res-at-point (event-point event))))
    (if cstr (mmlquery-goto-resdef (intern cstr) t)
      (message "No mmlquery resource at point"))))

(defun mizar-kbd-res-mmlquery (pos)
"Find the definition of the mmlquery resource at position POS in its
MMLQuery abstract."
  (interactive "d")
  (let ((cstr (mizar-res-at-point pos)))
    (if cstr (mmlquery-goto-resdef (intern cstr) t)
      (message "No mmlquery resource at point"))))



(defun mizar-kbd-cstr-tag (pos)
"Find the definition of the mmlquery resource at position POS."
  (interactive "d")
  (let ((cstr (mizar-res-at-point pos t)))
    (if cstr (mizar-symbol-def t cstr t)
      (message "No mmlquery resource at point"))))

(defun mizar-mouse-cstr-tag (event)
"Find the definition of the mmlquery resource we clicked on."
  (interactive "e")
  (select-window (event-window event))
  (let ((cstr (mizar-res-at-point (event-point event) t)))
    (if cstr (mizar-symbol-def t cstr t)
      (message "No mmlquery resource at point"))))


(defun mizar-highlight-constrs ()
  "Highlight the constructors in this buffer."
  (save-excursion
    (goto-char (point-min))
    (let ((props (list 'mouse-face 'highlight 'face 'underline)))
      (while (re-search-forward res-regexp (point-max) t)
	(add-text-properties (match-beginning 0) (match-end 0) props)))))

(defun mizar-set-mmlquery-properties (res)
"Set up the text property for mmlquery resource RES, in the same way
as used by the mmlquery browsing format.
Strings not matching `res-regexp' are just returned, while dot 
is replaced by space in matching."
(if (not (string-match res-regexp res))
    res
  (let ((map mmlquery-anchor-map)
	(res1 (replace-regexp-in-string "[.]" " " res)))
    (add-text-properties 0 (length res1)
			 (list 'mouse-face 'highlight 'face 'underline 
			       'fontified t local-map-kword map
			       'help-echo res
			       'anchor (intern res))
			   res1)
    res1)))

(defun mizar-intern-constrs-other-window (res)
"Display the constructors RES in buffer *Constructors list* in other window.
If `mizar-expl-kind' is 'mmlquery, then the constructors will be
displayed in the buffer *mmlquery*."
(let (cbuf)
  (cond 
   ((eq mizar-expl-kind 'mmlquery)
    (setq cbuf (get-buffer "*mmlquery*"))
    (unless (and cbuf (get-buffer-process cbuf))
      (mizar-run-mmlquery))
    (setq cbuf (get-buffer "*mmlquery*"))
    (set-buffer cbuf)
    (comint-kill-input)
    (insert res))
   (t
    (setq cbuf (get-buffer-create "*Constructors list*"))
    (set-buffer cbuf)
    (erase-buffer)
    (insert res)
    (mizar-highlight-constrs)
    (use-local-map mizar-cstr-map)
    (goto-char (point-min))))
  (switch-to-buffer-other-window cbuf)))

(defvar mmlquery-default-list-query-kw "atleast"
"The default mmlquery keyword for creating a query for a list of resources.")

(defun mizar-default-query-for-list (syms)
"Create the default query from a list of mmlquery resources SYMS."
 (concat mmlquery-default-list-query-kw "("
	 (mapconcat 'identity syms ",") ");"))

(defun mizar-transl-frm (frm)
"Translate FRM according to `mizar-expl-kind'."
(cond 
 ((eq mizar-expl-kind 'xml) frm)
 ((eq mizar-expl-kind 'raw) (frmrepr frm))
 ((eq mizar-expl-kind 'translate) (expfrmrepr frm))
 ((eq mizar-expl-kind 'constructors)
  (prin1-to-string (expfrmrepr frm t)))
 ((eq mizar-expl-kind 'sorted)
  (prin1-to-string (sort (unique (expfrmrepr frm t)) 'string<)))
 ((eq mizar-expl-kind 'mmlquery)
  (mizar-default-query-for-list
;;   (mapcar 'mizar-set-mmlquery-properties
   (mapcar '(lambda (x) (replace-regexp-in-string "[.]" " " x))
	   (sort (unique (expfrmrepr frm t)) 'string<))))
 (t "")))

(defun mizar-show-constrs-kbd (&optional pos)
  "Show constructors of the inference at point.
The constructors are translated according to the variable
`mizar-expl-kind', and shown in the buffer *Constructors list* or
*mmlquery* if `mizar-expl-kind' is 'mmlquery.  The variable
`mizar-do-expl' should be non-nil.  Argument POS is a buffer
position from which to begin this process; if nil, point is
used."
  (interactive)
  (let ((pos (or pos (point))))
    (save-excursion
    (let ((frm (get-text-property pos 'cexpl)))
      (if frm
	  (let ((res (mizar-transl-frm frm)))
	    (goto-char pos)
	    (mizar-intern-constrs-other-window res)))))))

(defun mizar-show-constrs-other-window (event)
  "Show constructors of the inference that was just clicked on.
The constructors are translated according to the variable 
`mizar-expl-kind', and shown in the buffer *Constructors list*
or *mmlquery* if `mizar-expl-kind' is 'mmlquery.
The variable `mizar-do-expl' should be non-nil."
  (interactive "e")
  (select-window (event-window event))
  (save-excursion
    (let ((frm (get-text-property (event-point event) 'cexpl)))
      (if frm
	  (let ((res (mizar-transl-frm frm)))		
	    (goto-char (event-point event))
	    (mizar-intern-constrs-other-window res))))))


;; modified from Lisp:wikiarea.el by EdwardOConnor
;; we should use url.el or http-get.el, when they make it into distros
;; wget is good, but requires Window$ users to download it
(defun mizar-get-http-file (bufname host request)
  "Fetch HTTP REQUEST from HOST, put result into buffer BUFNAME and return it.
Previous contents of BUFNAME is deleted."
  (if (get-buffer bufname) (kill-buffer bufname))
  (let* ((proc (open-network-stream "GetHTTP" bufname host 80))
         (buf (process-buffer proc)))
    (process-send-string proc (concat "GET " request " HTTP/1.0\r\n\r\n"))
    ;; Watch us spin and stop Emacs from doing anything else!
    (while (equal (process-status proc) 'open)
      (when (not (accept-process-output proc 180))
        (delete-process proc)
        (error "Network timeout!")))
    (delete-process proc)

    (with-current-buffer buf
      (goto-char (point-min))
      (if (looking-at "HTTP/[0-9.]+ \\([0-9]+\\) \\(.*\\)")
          (progn
            (forward-line 1)
            (while (looking-at "^.+[:].+")
              (forward-line 1))
            (forward-line 1)
            (delete-region (point-min) (point)))
        (error "Unable to fetch %s from %s." request host)))
    buf))

(defvar advisor-output "*Proof Advice*")

(defun mizar-ask-advisor ()
  "Send the contents of the *Constr Explanations* buffer to Mizar Proof Advisor.
Resulting advice is shown in the buffer *Proof Advice*, where normal tag-browsing
keyboard bindings can be used to view the suggested references."
  (interactive)
  (let* ((request (concat advisor-cgi "?Text=1\\&Limit=" 
			  (number-to-string advisor-limit)
			  "\\&Formula="
			  (query-handle-chars-cgi
			   (buffer-substring-no-properties
			    (point-min) (point-max)))))
	 (abuffer (mizar-get-http-file advisor-output advisor-server request)))
    (if abuffer
	(progn (switch-to-buffer-other-window abuffer)
	       (mizar-mode))
      (message "No references advised")))
  )

(defun mizar-toggle-cstr-expl (to)
  "Set `mizar-do-expl' to nil if TO is 'none, otherwise set
`mizar-expl-kind' to TO and `mizar-do-expl' to T."
  (cond ((eq to 'none) (setq  mizar-do-expl nil))
	(t (setq  mizar-expl-kind to
		  mizar-do-expl t))))




;; Code for access to the squery ring
;; mostly stolen from vc
;; (these history funcs should be done generically in some emacs library)
(defconst query-maximum-squery-ring-size 128
  "Maximum number of saved comments in the comment ring.")
(defvar query-squery-ring (make-ring query-maximum-squery-ring-size))
(defvar query-squery-ring-index nil)
(defvar query-last-squery-match nil)
(defvar query-entry-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\M-n" 'query-next-squery)
    (define-key map "\M-p" 'query-previous-squery)
    (define-key map "\M-r" 'query-squery-search-reverse)
    (define-key map "\M-s" 'query-squery-search-forward)
    (define-key map "\C-c\C-c" 'query-send-entry)
    (define-key map "\C-c\C-m" 'query-send-to-mmlquery)
    map)
"Keymap in the *MML Query Input* buffer.
Used for sending queries to MML Query server and browsing and searching
previous queries.
Commands:
\\{query-entry-map}"
)

(defun query-entry-mode ()
  "Minor mode for sending MML Queries.
These bindings are added to the global keymap when you enter this mode:
\\[query-send-entry]	send the query to MML Query

Whenever you send a query, it is added to a ring of
saved queries.  These can be recalled as follows:

\\[query-next-squery]	replace region with next message in squery ring
\\[query-previous-squery]	replace region with previous message in squery ring
\\[query-squery-search-reverse]	search backward for regexp in the squery ring
\\[query-squery-search-forward]	search backward for regexp in the squery ring

Entry to the query-entry submode calls the value of `text-mode-hook', then
the value of query-entry-mode-hook."
  (interactive)
  (set-syntax-table text-mode-syntax-table)
  (use-local-map query-entry-map)
  (setq local-abbrev-table text-mode-abbrev-table)
  (setq major-mode 'query-entry-mode)
  (setq mode-name "Query-entry")
  (make-local-variable 'query-squery-ring-index)
  (set-buffer-modified-p nil)
  (setq buffer-file-name nil)
  (run-hooks 'text-mode-hook 'query-entry-mode-hook)
)

(defun query-start-entry ()
"Start a new query in buffer *MML Query input*."
  (interactive)
  (let ((buf  (or (get-buffer "*MML Query input*")
		  (get-buffer-create "*MML Query input*"))))
    (pop-to-buffer buf)
    (erase-buffer)
    (if (not (eq major-mode 'query-entry-mode))
	(query-entry-mode)))
  (message "Enter a query. Type C-c C-c when done.")
)

(defun alfanump (nr)
  "Determine whether the integer NR represents an alphabetic or
numeric character."
  (or (and (< nr 123) (< 96 nr))
      (and (< nr 91) (< 64 nr))
      (and (< nr 58) (< 47 nr))))

(defun query-handle-chars-cgi (str)
"Replace non-alphanumeric chars in STR by %code."
(let ((slist (string-to-list str))
      (space (nreverse (string-to-list (format "%%%x" 32))))
      (nl (nreverse (string-to-list "%0A")))
      res codel)
  (if (eq mizar-emacs 'xemacs)
      (setq slist (mapcar 'char-to-int slist)))
  (while slist
    (let ((i (car slist)))
      (cond ((alfanump i)
	     (setq res (cons i res)))
	    ((member i '(32 9)) ; 10 9 13))        ; "[ \n\t\r]"
	     (setq res (append space res)))
	    ((member i '(10 13)) ; 10 9 13))        ; "[ \n\t\r]"
	     (setq res (append nl res)))
	    (t
	     (setq codel (nreverse (string-to-list (format "%x" i))))
	     (setq res (nconc codel (cons 37 res))))))
    (setq slist (cdr slist)))
  (concat (nreverse res))))



(defun query-send-entry ()
  "Send the contents of the current buffer to MML Query."
  (interactive)
  (ring-insert query-squery-ring (buffer-string))
  (let ((query (concat query-url "emacs_search?input="
		     (query-handle-chars-cgi (buffer-string)))))
  (if query-text-output
      (setq query (concat query "&text=1")))
  (mizar-ask-query query)))

(defun query-send-to-mmlquery ()
  "Send the contents of the current buffer to the local mmlquery
server, start it if not running."
  (interactive)
  (let ((query (buffer-string)))
    (ring-insert query-squery-ring query)
    (unless (get-buffer "*mmlquery*")
      (mizar-run-mmlquery)
      (sleep-for 0.5))
    (let ((mbuf (get-buffer "*mmlquery*")))
      (process-send-string (get-process "mmlquery") 
			   (concat query "\n"))
      (pop-to-buffer mbuf))))

(defun query-previous-squery (arg)
  "Cycle backwards through query-squery history.
With a numeric prefix ARG, go back ARG queries."
  (interactive "*p")
  (let ((len (ring-length query-squery-ring)))
    (cond ((<= len 0)
	   (message "Empty query-squery ring")
	   (ding))
	  (t
	   (erase-buffer)
	   ;; Initialize the index on the first use of this command
	   ;; so that the first M-p gets index 0, and the first M-n gets
	   ;; index -1.
	   (if (null query-squery-ring-index)
	       (setq query-squery-ring-index
		     (if (> arg 0) -1
			 (if (< arg 0) 1 0))))
	   (setq query-squery-ring-index
		 (mod (+ query-squery-ring-index arg) len))
	   (message "%d" (1+ query-squery-ring-index))
	   (insert (ring-ref query-squery-ring query-squery-ring-index))))))

(defun query-next-squery (arg)
  "Cycle forward through comment history.
With a numeric prefix ARG, go forward ARG queries."
  (interactive "*p")
  (query-previous-squery (- arg)))

(defun query-squery-search-reverse (str)
  "Search backward through squery history for substring match of STR."
  (interactive "sPrevious query matching (regexp): ")
  (if (string= str "")
      (setq str query-last-squery-match)
    (setq query-last-squery-match str))
  (if (null query-squery-ring-index)
      (setq query-squery-ring-index -1))
  (let ((len (ring-length query-squery-ring))
	(n (1+ query-squery-ring-index)))
    (while (and (< n len) (not (string-match str (ring-ref query-squery-ring n))))
      (setq n (+ n 1)))
    (cond ((< n len)
	   (query-previous-squery (- n query-squery-ring-index)))
	  (t (error "Not found")))))

(defun query-squery-search-forward (str)
  "Search forwards through squery history for substring match of STR."
  (interactive "sNext query matching (regexp): ")
  (if (string= str "")
      (setq str query-last-squery-match)
    (setq query-last-squery-match str))
  (if (null query-squery-ring-index)
      (setq query-squery-ring-index 0))
  (let ((len (ring-length query-squery-ring))
	(n query-squery-ring-index))
    (while (and (>= n 0) (not (string-match str (ring-ref query-squery-ring n))))
      (setq n (- n 1)))
    (cond ((>= n 0)
	   (query-next-squery (- n query-squery-ring-index)))
	  (t (error "Not found")))))

;;;;;;;;;; Inferior mmlquery mode ;;;;;;;;;;

(defcustom mmlquery-program-name "/nfs/megrez/bin/mmlquery"
  "Path to the mmlquery program."
  :type 'string
  :group 'mizar-mml-query)

(defvar mmlquery-prompt-regexp "^mmlquery> *")
(defvar inferior-mmlquery-mode-map nil)
(defvar inferior-mmlquery-mode-syntax-table nil)
(defvar mmlquery-output-buffer "*MMLQuery Output*")


(if inferior-mmlquery-mode-syntax-table
    ()
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?_ "w" table)
    (setq inferior-mmlquery-mode-syntax-table table)))

(defvar mmlquery-pending-output "")

(defun inferior-mmlquery-mode-variables ()
  "Set up variables used in inferior-mmlquery-mode."
  (set-syntax-table inferior-mmlquery-mode-syntax-table)
  (setq mmlquery-pending-output "")
)

(defun mmlquery-finished (str)
  (string-match mmlquery-prompt-regexp str))

(defun mmlquery-handle-output (str)
  (cond 
   ((mmlquery-finished str)
    (save-excursion
      (set-buffer (get-buffer-create mmlquery-output-buffer))
      (erase-buffer)
      (insert mmlquery-pending-output)
      (setq mmlquery-pending-output "")
      (insert str)
      (kill-line -1)  ;; remove the prompt
      (mmlquery-decode (point-min) (point-max))
      (display-buffer mmlquery-output-buffer))
    "mmlquery> ")
   (t
    (setq mmlquery-pending-output (concat mmlquery-pending-output str))
    "")))

;; reserved for mmlquery-specific bindings
(defun inferior-mmlquery-mode-commands (map) nil)

(defun inferior-mmlquery-mode ()
  "Major mode for interacting with an inferior Mmlquery process.

The following commands are available:
\\{inferior-mmlquery-mode-map}

Entry to this mode calls the value of
`inferior-mmlquery-mode-hook' with no arguments, if that value is
non-nil.  Likewise with the value of `comint-mode-hook'.
`inferior-mmlquery-mode-hook' is called after `comint-mode-hook'.

You can send text to the inferior Mmlquery from other buffers
using the commands `send-region', `send-string' and
\\[mmlquery-consult-region].

Commands:

Return at end of buffer sends line as input.

Return not at end copies rest of line to end and sends it.

\\[comint-kill-input] and \\[backward-kill-word] are kill
commands, imitating normal Unix input editing.

\\[comint-interrupt-subjob] interrupts the shell or its current subjob if any.

\\[comint-stop-subjob] stops.  \\[comint-quit-subjob] sends quit
signal."
  (interactive)
  (require 'comint)
  (comint-mode)
  (setq major-mode 'inferior-mmlquery-mode
	mode-name "Inferior Mmlquery"
	comint-prompt-regexp mmlquery-prompt-regexp)
  (inferior-mmlquery-mode-variables)
  (if inferior-mmlquery-mode-map nil
    (setq inferior-mmlquery-mode-map (copy-keymap comint-mode-map))
    (inferior-mmlquery-mode-commands inferior-mmlquery-mode-map))
  (use-local-map inferior-mmlquery-mode-map)
  (run-hooks 'inferior-mmlquery-mode-hook))

(defun mizar-run-mmlquery ()
  "Run an inferior Mmlquery process, I/O via buffer *mmlquery*."
  (interactive)
  (require 'comint)
  (or (executable-find mmlquery-program-name)
      (error "Mmlquery is not executable: %s" mmlquery-program-name))
  (switch-to-buffer 
   (make-comint "mmlquery" mmlquery-program-name 
		nil "--present=emacs" ))
  (add-hook 'comint-preoutput-filter-functions 'mmlquery-handle-output)
  (inferior-mmlquery-mode))

;;;;;;;;;;; MMLQuery browsing

(defvar mmlquery-mode nil
  "True if Mmlquery mode is in use.")

(make-variable-buffer-local 'mmlquery-mode)
(put 'mmlquery-mode 'permanent-local t)

(defcustom mmlquery-mode-hook nil
  "Functions to run when entering Mmlquery mode."
  :type 'hook
  :group 'mmlquery)

(defcustom mmlquery-underlines-highlited t
  "If non-nil, the highlighted links in GAB's are also underlined."
  :type 'boolean
  :group 'mizar-mml-query)

(defvar mmlquery-mode-map nil
  "Keymap for mmlquery minor mode.")

(defvar mmlquery-mode-menu nil
  "Menu for mmlquery minor mode.")


(if mmlquery-mode-map
    nil
  (setq mmlquery-mode-map (make-sparse-keymap))
  (define-key mmlquery-mode-map "\C-cn" 'mmlquery-next)
  (define-key mmlquery-mode-map "\C-cp" 'mmlquery-previous)
  (easy-menu-define mmlquery-mode-menu
    mmlquery-mode-map
    "Menu used when mmlquery minor mode is active."
    '("MML Query"	    
	    ["Next" mmlquery-next :active (< 0 mmlquery-history-position)
	    :help "Go to the next mmlquery definition"]	    
	    ["Previous" mmlquery-previous :active 
              (< (+ 1 mmlquery-history-position) (ring-length mmlquery-history))
	    :help "Go to the previous definition"]
	    ("Items displayed in browser"	    
	     ["Definitional theorems" mmlquery-toggle-def :style radio 
	      :selected (not (memq 'mmlquery-def buffer-invisibility-spec)) :active t
	      :help "Toggle hiding of definitional theorems" ]
	      ["Definienda" mmlquery-toggle-dfs :style radio :selected 
	      (not (memq 'mmlquery-dfs buffer-invisibility-spec)) :active t
	      :help "Toggle hiding of constructor definienda" ]
	     ["Property formulas" mmlquery-toggle-property-hiding 
	      :style radio :selected (not mmlquery-properties-hidden) :active t
	      :help "Hide/Show all property formulas" ]
	     ["Existential clusters" (mmlquery-toggle-hiding 'mmlquery-exreg) :style radio 
	      :selected (not (memq 'mmlquery-exreg buffer-invisibility-spec)) :active t
	      :help "Toggle hiding of existential clusters" ]
	     ["Functor clusters" (mmlquery-toggle-hiding 'mmlquery-funcreg) :style radio 
	      :selected (not (memq 'mmlquery-funcreg buffer-invisibility-spec)) :active t
	      :help "Toggle hiding of functor clusters" ]
	     ["Conditional clusters" (mmlquery-toggle-hiding 'mmlquery-condreg) :style radio 
	      :selected (not (memq 'mmlquery-condreg buffer-invisibility-spec)) :active t
	      :help "Toggle hiding of conditional clusters" ]	
	      ["Theorems" (mmlquery-toggle-hiding 'mmlquery-th) :style radio 
	      :selected (not (memq 'mmlquery-th buffer-invisibility-spec)) :active t
	      :help "Toggle hiding of theorems" ]
	     ))))

(or (assq 'mmlquery-mode minor-mode-map-alist)
    (setq minor-mode-map-alist
          (cons (cons 'mmlquery-mode mmlquery-mode-map)
                minor-mode-map-alist)))
(or (assq 'mmlquery-mode minor-mode-alist)
    (setq minor-mode-alist
	  (cons '(mmlquery-mode " MMLQuery")
		minor-mode-alist)))


(defvar mmlquery-tool-bar-map
  (if (and (functionp 'display-graphic-p)
	   (display-graphic-p))
      (let ((tool-bar-map (make-sparse-keymap)))
;	(tool-bar-add-item-from-menu 'Info-exit "close" Info-mode-map)
	(tool-bar-add-item-from-menu 'mmlquery-previous "left_arrow" mmlquery-mode-map)
	(tool-bar-add-item-from-menu 'mmlquery-next "right_arrow" mmlquery-mode-map)
 	(tool-bar-add-item-from-menu 'mmlquery-toggle-def "cut" mmlquery-mode-map)
 	(tool-bar-add-item-from-menu 'mmlquery-toggle-dfs "preferences" mmlquery-mode-map)
	(tool-bar-add-item-from-menu 'mmlquery-toggle-property-hiding "paste" 
				     mmlquery-mode-map)
;; 	(tool-bar-add-item-from-menu 'Info-top-node "home" Info-mode-map)
;; 	(tool-bar-add-item-from-menu 'Info-index "index" Info-mode-map)
;; 	(tool-bar-add-item-from-menu 'Info-goto-node "jump_to" Info-mode-map)
;; 	(tool-bar-add-item-from-menu 'Info-search "search" Info-mode-map)
	tool-bar-map)))




(defun mmlquery-mode (&optional arg)
  "Minor mode for browsing text/mmlquery files.
These are files with embedded formatting information in the MIME
standard text/mmlquery format.  Turning the mode on runs
`mmlquery-mode-hook'.

If the optional argument ARG is non-nil, turn off mmlquery-mode.

Commands:

\\<mmlquery-mode-map>\\{mmlquery-mode-map}"
  (interactive "P")
  (let ((mod (buffer-modified-p)))
    (cond ((or (<= (prefix-numeric-value arg) 0)
	       (and mmlquery-mode (null arg)))
	   ;; Turn mode off
	   (easy-menu-remove mmlquery-mode-menu) ; xemacs only
	   (setq mmlquery-mode nil)
	   (setq buffer-file-format (delq 'text/mmlquery buffer-file-format)))
	  
	  (mmlquery-mode nil)		; Mode already on; do nothing.

	  (t (setq mmlquery-mode t)	; Turn mode on
	     (mizar-mode)               ; Turn on mizar-mode
	     (hs-minor-mode -1)         ; Turn off hs-minor-mode
	     (add-to-list 'buffer-file-format 'text/mmlquery)
	     (add-to-list 'fontification-functions 'mmlquery-underline-highlited)
	
	     (make-local-variable 'font-lock-fontify-region-function)
	     (make-local-variable 'mmlquery-properties-hidden)
	     (set (make-local-variable 'tool-bar-map) mmlquery-tool-bar-map)
	     (let ((oldfun font-lock-fontify-region-function))
	       (setq font-lock-fontify-region-function
		     `(lambda (beg end loudly) 
			(,oldfun beg end loudly)
		       (mmlquery-underline-in-region beg end))))	

	     (mmlquery-underline-highlited 0)
	     (mmlquery-default-invisibility)
	     (easy-menu-add mmlquery-mode-menu) ; for xemacs only
	     (run-hooks 'mmlquery-mode-hook)))
    (set-buffer-modified-p mod)
    (force-mode-line-update)))



;; Reading .gab files

;; The .gab files contain anchors and definitions. 
;; During parsing, the text properties are set for anchors,
;; while definitions are used to save their position as symbol
;; property 'mmlquery-definition or 'mmlquery-redef .
;; Additionaly the mmlquery kind (e.g. pred, prednot, attr, etc.) 
;; is also kept as the value of the symbol property 'mmlquery-kind .
;; All the text of definitions also gets the value of its name's
;; 'mmlquery-kind as a text property, and also its 'invisible text
;; property gets this 'mmlquery-kind as a value.


;; If the 'definition property is missing from a symbol, we 
;; open the .gab file containing the symbol first.


;; Parsing  completely stolen from enriched.el

;; We use a lot of invisibility
(put 'invisible 'format-list-valued t)

(defconst mmlquery-annotation-regexp "<\\(/\\)?\\([-A-Za-z0-9]+\\)>"
  "Regular expression matching mmlquery-text annotations.")

(defconst mmlquery-translations
  '(
;;    (mouse-face    (highlight   "a"))		   
    (PARAMETER     (t           "p")) ; Argument of preceding annotation
    ;; The following are not part of the standard:
    (FUNCTION      (mmlquery-decode-anchor "a")
		   (mmlquery-decode-definition "l")
		   (mmlquery-decode-property     "r")
		   (mmlquery-decode-query "q")
		   (mmlquery-decode-hidden "h")) ; generic hidden
    (read-only     (t           "x-read-only"))
    (unknown       (nil         format-annotate-value))
)
  "List of definitions of text/mmlquery annotations.
See `format-annotate-region' and `format-deannotate-region' for the definition
of this structure.")


(defvar mmlquery-anchor-map
  (let ((map (make-sparse-keymap))
	(button_kword (if (eq mizar-emacs 'xemacs) [button2]
			[mouse-2])))
    (set-keymap-parent map mizar-mode-map)
    (define-key map button_kword 'mmlquery-goto-def-mouse)
    (define-key map "\C-m"  'mmlquery-goto-def)
    map)
"Keymap used at mmlquery anchors.")


(defun mmlquery-decode-anchor (start end &optional param)
  "Decode an anchor property for text between START and END.
PARAM is a `<p>' found for the property.
Value is a list `(START END SYMBOL VALUE)' with START and END denoting
the range of text to assign text property SYMBOL with value VALUE "
  (let ((map mmlquery-anchor-map))
    (add-text-properties start end 
			 (list 'mouse-face 'highlight 'face 'underline 
			       'fontified t local-map-kword map
			       'help-echo param))
    (list start end 'anchor (intern param))))


(defun get-mmlquery-resource-article (sym)
"Extract the article name from a mmlquery resource symbol SYM, append '.gab'."
  (let ((sname (symbol-name sym)))
    (unless (string-match res-regexp sname)
      (error "Error: all mmlquery resources are supposed to match %s: %s %S" 
	     res-regexp sname sym))
    (concat (downcase (match-string 1 sname)) ".gab")))

(defvar mmlquery-item-starter-map
  (let ((map (make-sparse-keymap))
	(button_kword (if (eq mizar-emacs 'xemacs) [button2]
			[mouse-2])))
    (set-keymap-parent map mizar-mode-map)
    (define-key map button_kword 'mmlquery-toggle-item-invis-mouse)
    (define-key map "\C-m"  'mmlquery-toggle-item-invis)
    map)
"Keymap used at mmlquery item starters.")

(defvar mmlquery-item-starter-help
(substitute-command-keys "\\<mmlquery-item-starter-map>\\[mmlquery-toggle-item-invis-mouse] or \\<mmlquery-item-starter-map>\\[mmlquery-toggle-item-invis]: Hide/Show items of this kind")
"Help displayed at mmlquery item starters.")

(defun mmlquery-decode-definition (start end &optional param &rest params)
  "Decode a definition property for text between START and END.
PARAM is a `<p>' found for the property.
Value is a list `(START END SYMBOL VALUE)' with START and END denoting
the range of text to assign text property SYMBOL with value VALUE .
The definition text now must start with :: PARAM, with the dot in
PARAM replaced with space.  Additional parameters can be given by using PARAMS."
(let ((sym (intern param)) 
      (dstart (+ start 3 (length param))) ;; 3 = length ":: "
      (map mmlquery-item-starter-map)
      (allparams (cons param params))
      kind name pname)
  (setq name (buffer-substring-no-properties start dstart))
  (unless (string-match res-regexp param)
    (error "Error: all mmlquery resources are supposed to match %s: %s" 
	   res-regexp param))
  (setq kind (intern (concat "mmlquery-" (match-string 2 param)))
	pname (concat ":: " (replace-match " " nil nil param 3)))
  (unless (string-equal name pname)
    (error "Error: the first parameter must match the item name %s: %s"
	   pname name))

  (while allparams
    (let* ((par (car allparams))
	   (sym1 (intern par)))
      (cond 
;; The first def in its article is the 'true' original for us 
       ((and (not (get sym1 'mmlquery-definition))
	     (equal (file-name-nondirectory (buffer-file-name 
					     (current-buffer)))
		    (get-mmlquery-resource-article sym1)))
	;; we use the matching done in get-mmlquery-resource-article
	(let ((kind1 (intern (concat "mmlquery-" (match-string 2 par)))))
	  (put sym1 'mmlquery-definition start)
	  (put sym1 'mmlquery-kind kind1))
	)
       (t
;; otherwise it is stored among redefinitions - this is unused now
	(put sym1 'mmlquery-redef (cons start (get sym1 'mmlquery-redef)))
	)))
    (setq allparams (cdr allparams)))
  (incf dstart)  ;; this believs that end of line follows
  (add-text-properties (+ 3 start) dstart
		       (list 'mouse-face  'highlight ; 'speedbar-selected-face   ; 'highlight ;'face 'underline 
;			     'fontified t 
;			     'face '(:underline t)
			     local-map-kword map
			     'help-echo mmlquery-item-starter-help
			     'mmlquery-item-starter kind))
  (put-text-property dstart end 'mmlquery-kind kind)
  (list dstart end 'invisible kind)))

(defvar mmlquery-property-map
  (let ((map (make-sparse-keymap))
	(button_kword (if (eq mizar-emacs 'xemacs) [button2]
			[mouse-2])))
    (set-keymap-parent map mizar-mode-map)
    (define-key map button_kword 'mmlquery-toggle-property-invis-mouse)
    (define-key map "\C-m"  'mmlquery-toggle-property-invis)
    map)
"Keymap used at mmlquery properties.")

(defvar mmlquery-property-help
(substitute-command-keys "\\<mmlquery-property-map>\\[mmlquery-toggle-property-invis-mouse] or \\<mmlquery-property-map>\\[mmlquery-toggle-property-invis]: Hide/Show the property formula")
"Help displayed at mmlquery properties.")

(defun mmlquery-decode-property (start end &optional param)
  "Decode a 'property property for text between START and END.
PARAM is a `<p>' found for the property and must be nil.
Value is a list `(START END SYMBOL VALUE)' with START and END denoting
the range of text to assign text property SYMBOL with value VALUE"
  (let ((map mmlquery-property-map)
	(text (buffer-substring-no-properties start end)))
    (or (string-match "^\\([a-z]+\\);" text)
	(error "Error: all properties are supposed to match \"^[a-z]+$\": %s" param))
    (let ((prop (match-string 1 text)))
      (add-text-properties start (+ start (length prop))
			   (list 'mouse-face 'highlight 'face 'underline 
				 'fontified t local-map-kword map
				 'help-echo mmlquery-property-help))
      (list start end 'mmlquery-property (intern (concat "mmlquery-" prop))))))


(defun mmlquery-decode-hidden (start end &optional param)
  "Decode a hidden property for text between START and END.
PARAM is a `<p>' found for the property.
Value is a list `(START END SYMBOL VALUE)' with START and END denoting
the range of text to assign text property SYMBOL with value VALUE"
  (unless (string-match "^[a-z]+$" param)
    (error "Error: all properties are supposed to match \"^[a-z]+$\": %s" param))
  (let ((invis (get-text-property start 'invisible))
	(kind (intern  (concat "mmlquery-" param))))
    (put-text-property start end 'mmlquery-property-fla t)
    (list start end 'invisible 'mmlquery-property)
))

(defun mmlquery-decode-query (start end &optional param)
  "Decode a query property for text between START and END.
PARAM is a `<p>' found for the property.
Value is a list `(START END SYMBOL VALUE)' with START and END denoting
the range of text to assign text property SYMBOL with value VALUE"
(let ((query param))
  (list start end 'query query)))

(defconst mmlquery-parsing-progress-step 2048
"Number of chars to process before the next parsing progress report.")

(defun mmlquery-next-annotation ()
  "Find and return next text/mmlquery annotation.
Any \"<<\" strings encountered are converted to \"<\".
Return value is \(begin end name positive-p), or nil if none was found."
  (while (and (search-forward "<" nil 1)
	      (progn (goto-char (match-beginning 0))
		     (not (looking-at mmlquery-annotation-regexp))))
    (forward-char 1)
    (if (= ?< (char-after (point)))
	(delete-char 1)
      ;; A single < that does not start an annotation is an error,
      ;; which we note and then ignore.
      (message "Warning: malformed annotation in file at %s" 
	       (1- (point)))))
  (if (not (eobp))
      (let* ((beg (match-beginning 0))
	     (end (match-end 0))
	     (name (downcase (buffer-substring 
			      (match-beginning 2) (match-end 2))))
	     (pos (not (match-beginning 1))))
	(mizar-step-progress beg "Parsing" 
			     mmlquery-parsing-progress-step)
	(list beg end name pos))))


(defun mmlquery-remove-header ()
  "Remove file-format header at point."
  (while (looking-at "^::[ \t]*Content-[Tt]ype: .*\n")
    (delete-region (point) (match-end 0)))
  (if (looking-at "^\n")
      (delete-char 1)))

(defun mmlquery-decode (from to)
  "Decode the results of the query, as delimited by FROM and TO."
  (save-excursion
    (save-restriction
      (narrow-to-region from to)
      (goto-char from)
      (mmlquery-remove-header)
      ;; Translate annotations
      (mizar-progress-start)
      (format-deannotate-region from (point-max) mmlquery-translations
				'mmlquery-next-annotation)
      (mizar-progress-done)
      (point-max))))


(defun mmlquery-abstract-p (x)
"Non nil if buffer X is mmlquery abstract."
(let ((name  (buffer-file-name x)))
  (and (stringp name)
       (string-match "\.gab$" name))))

;;;; The browsing functions

(defvar mmlquery-history-size 512
"*Size of the mmlquery history ring.
When this is reached, the oldest element is forgotten.")

(defvar mmlquery-history-position -1
"Our position in `mmlquery-history'.
Has to be updated with any operation on `mmlquery-history'.")

(defvar mmlquery-history (make-ring mmlquery-history-size)
  "History of definitions user has visited.
It has a browser-like behavior: going from the middle of it
to something different from its successor causes the whole
successor list to be forgotten.
Each element of the history is a list
\(buffer file-name position), if buffer was killed and file-name exists, we re-open the file.")

      
(defun ring-delete-from (ring index)
"Delete all RING elements starting from INDEX (including it).
INDEX = 0 is the most recently inserted; higher indices
correspond to older elements.
If INDEX > RING length, do nothing and return nil, otherwise 
return the new RING length."
(if (< index (ring-length ring))
;; This could be done more efficiently
(let ((count (+ 1 index)))
  (while (< 0 count)
    (ring-remove ring 0)
    (decf count))
  (ring-length ring))))


(defun mmlquery-goto-def (&optional pos)
"Go to the definition of the mmlquery resource at point or POS if given."
  (interactive "d")
  (let* ((anch (get-text-property (or pos (point)) 'anchor)))
    (unless anch (error "No mmlquery reference at point!"))
    (mmlquery-goto-resdef anch t)))

(defun mmlquery-goto-def-mouse (event)
"Go to to the definition of the mmlquery resource we clicked on."
  (interactive "e")
  (select-window (event-window event))
  (let* ((anch (get-text-property (event-point event) 'anchor)))
    (unless anch (error "No mmlquery reference at point!"))
    (mmlquery-goto-resdef anch t)))


(defun mmlquery-goto-resdef (anch &optional push)
"Go to the definition of ANCH. 
If PUSH, push positions onto the `mmlquery-history'."
  (let*
      ((aname (get-mmlquery-resource-article anch))
       (afile (concat mmlquery-abstracts aname))
       (defpos (or (get anch 'constructor) 
		   (get anch 'mmlquery-definition)))
       (oldbuf (current-buffer))
       (oldfile (buffer-file-name (current-buffer)))
       (oldpos (point)))
;; Load the article if not yet
    (unless defpos
      (message "Parsing abstract %s ..." aname)
      (find-file-noselect afile)
      (setq defpos (get anch 'mmlquery-definition)))
    (unless defpos (error "No mmlquery definition for resource %S" anch))
;; The abstract may have been killed
    (unless (get-file-buffer afile)
      (message "Parsing abstract %s ..." aname))
    (find-file afile)
    (goto-char defpos)
    (if push
	(progn
;; Forget the forward part of history
;; This delees the mmlquery-history-position too
	  (if (<= 0 mmlquery-history-position)
	      (ring-delete-from mmlquery-history 
				mmlquery-history-position))
;; Fix the previous position too - we deleted it above
	  (ring-insert mmlquery-history (list oldbuf oldfile oldpos))
	  (ring-insert mmlquery-history 
		       (list (current-buffer) afile defpos))
	  (setq mmlquery-history-position 0)))
    anch))


(defun mmlquery-goto-history-pos (history-pos)
"Go to the history position HISTORY-POS, trying to re-open the file
if killed in the meantime. Error if it is in temporary buffer,
which was killed."
(if (buffer-live-p (car history-pos))
    (switch-to-buffer (car history-pos))
  (if (cadr history-pos)
      (find-file (cadr history-pos))
    (error "Cannot go back because the temporary buffer was deleted.")))
(goto-char (third history-pos)))


(defun mmlquery-previous ()
  "Go back to the previous mmlquery definition visited
before `mmlquery-history-position', and change this variable.
If `mmlquery-history-position' is 0, i.e. we just start using
the history, add the current position into `mmlquery-history', 
to be able to return here with `mmlquery-next'."
  (interactive)
;; Initialy the ring-length is 0 and mmlquery-history-position is -1
  (if (<= (ring-length mmlquery-history) (+ 1 mmlquery-history-position))
      (message "No previous definitions visited.")

    (incf mmlquery-history-position)
    (mmlquery-goto-history-pos (ring-ref mmlquery-history 
					 mmlquery-history-position))))

(defun mmlquery-next ()
  "Go forward to the next mmlquery definition visited
before `mmlquery-history-position', and change this variable."
  (interactive)
;; Initialy the ring-length is 0 and mmlquery-history-position is -1
  (if (<= mmlquery-history-position 0)
      (message "No next definitions visited.")
    (decf mmlquery-history-position)
    (mmlquery-goto-history-pos (ring-ref mmlquery-history 
					 mmlquery-history-position))))

(defcustom mmlquery-default-hidden-kinds
  (list 'mmlquery-def 'mmlquery-dfs 'mmlquery-property)
"*List of item kinds that get hidden upon loading of mmlquery abstracts."
:type '(repeat symbol)
:group 'mizar-mml-query)


(defun mmlquery-default-invisibility ()
  "Set up the initial, default invisibility specs for mmlquery."
  (dolist (sym mmlquery-default-hidden-kinds)
    (add-to-invisibility-spec sym)))



;; Borrowed from lazy-lock.el.
;; We use this to preserve or protect things when modifying text properties.
(defmacro save-buffer-state (varlist &rest body)
  "Bind variables according to VARLIST and eval BODY restoring buffer state."
  `(let* ,(append varlist
		  '((modified (buffer-modified-p)) (buffer-undo-list t)
		    (inhibit-read-only t) (inhibit-point-motion-hooks t)
		    (inhibit-modification-hooks t)
		    deactivate-mark buffer-file-name buffer-file-truename))
     ,@body
     (when (and (not modified) (buffer-modified-p))
       (set-buffer-modified-p nil))))

;; Not working yet, don't know why
;; (defun mmlquery-underlined-face (face)
;; "Return the underlined equivalent of symbol 'FACE. 
;; If it does not exist, create it and store as a property
;; 'mmlquery-underlined of 'FACE ."
;; (if face   
;;     (if (face-underline-p face) face
;;       (let ((fc1 (get face 'mmlquery-underlined)))
;; 	(if fc1 fc1
;;  	  (let ((fc2 
;; 		 (face-name 
;; 		  (copy-face face (intern (concat (symbol-name face) 
;; 						  "-underl"))))))
;; ;	    (set-face-attribute fc2 nil :underline t)
;;  	    (set-face-underline-p fc2 t)
;;  	    (put face 'mmlquery-underlined fc2)
;;  	    fc2)
;; )))
;;    'underline))

(defun mmlquery-underline-highlited (start)
"Add 'underline to 'highlite.
Only if `mmlquery-underlines-highlited' is non-nil.  Begin doing this at buffer position START."
(if mmlquery-underlines-highlited
    (save-buffer-state 
     nil
     (save-excursion
       (goto-char start)
       (while (not (eobp))
	 (let ((mfprop (get-text-property (point) 'mouse-face))
	       (next-change
		(or (next-single-property-change (point) 'mouse-face 
						 (current-buffer))
		    (point-max))))
	   (if (and (eq mfprop 'highlight)
		    (not (get-text-property (point) 'face)))
	       (put-text-property (point) next-change 'face 'underline))
;	       (let ((face (get-text-property (point) 'face)))
;		 (setq face (mmlquery-underlined-face face))
;		 (put-text-property (point) next-change 'face face);'(:underline "red");'underline
;;))
	   (goto-char next-change)))))))

(defun mmlquery-underline-in-region (beg end)
  (mmlquery-underline-highlited beg))


(defun mmlquery-toggle-hiding (sym)
  "Toggle whether we hide the symbol SYM."
  (if (memq sym buffer-invisibility-spec)
      (remove-from-invisibility-spec sym)
    (add-to-invisibility-spec sym))
  (redraw-frame (selected-frame)))   ; Seems needed

(defun mmlquery-toggle-dfs ()
  "Toggle whether definitions are hidden."
  (interactive)
  (mmlquery-toggle-hiding 'mmlquery-dfs))

(defun mmlquery-toggle-def ()
  "Toggle whether definitions are hidden."
  (interactive)
  (mmlquery-toggle-hiding 'mmlquery-def))

(defun mmlquery-toggle-item-invis (&optional pos)
"Toggle hiding of the mmlquery items that are of same kind as
the item at POS."
(interactive)
(let* ((pos (or pos (point))) 
       (prop (get-text-property pos 'mmlquery-item-starter)))
  (or prop (error "No MMLQuery item starter at point!"))
  (goto-char pos)
  (mmlquery-toggle-hiding prop)))

(defun mmlquery-toggle-item-invis-mouse (event)
"Calls `mmlquery-toggle-item-invis at the point we clicked on."
  (interactive "e")
  (select-window (event-window event))
  (mmlquery-toggle-item-invis (event-point event)))

(defun mmlquery-toggle-property-invis (&optional pos force)
"Toggle hiding of the property formula at POS.
Non-nil FORCE can be either 'hide or 'unhide, and then this
function is used to force the hiding state."
  (interactive)
  (save-buffer-state nil
  (let* ((pos (or pos (point)))
	 (propval (get-text-property pos 'mmlquery-property))
	 next-change start invis)
    (or propval (error "No MMLQuery expression at point!"))
    (goto-char pos)
    (setq next-change
	  (or (next-single-property-change pos 'mmlquery-property (current-buffer))
	      (point-max)))
    (or (get-text-property (- next-change 1)  'mmlquery-property-fla)
	(error "No property formula available for this property!"))
    (setq start (next-single-property-change pos 'mmlquery-property-fla 
					     (current-buffer) next-change))
    (setq invis (get-text-property start 'invisible))
    (if  (memq 'mmlquery-property invis)
	(setq invis (delq 'mmlquery-property invis))
      (setq invis (cons 'mmlquery-property invis)))
    (put-text-property start  next-change 'invisible invis))))

(defun mmlquery-toggle-property-invis-mouse (event)
"Toggle hiding of the property formula we clicked on."
  (interactive "e")
  (select-window (event-window event))
  (mmlquery-toggle-property-invis (event-point event)))


(defvar mmlquery-properties-hidden t
"Tells the property hiding for mmlquery abstracts.  Is buffer-local there.")

(defun mmlquery-toggle-property-hiding ()
"Force all property formulas to be either hidden or not,
according to current value of the flag `mmlquery-properties-hidden'.
Toggle the flag afterward."
(interactive)
(save-buffer-state nil
(save-excursion
  (setq mmlquery-properties-hidden (not mmlquery-properties-hidden))
  (goto-char (point-min))
  (while (not (eobp))
    (let ((mfprop (get-text-property (point) 'mmlquery-property-fla))
	  (next-change
	   (or (next-single-property-change (point) 'mmlquery-property-fla 
					    (current-buffer))
	       (point-max))))
      (if mfprop
	  (let (doit (invis (get-text-property (point) 'invisible)))
	    (if mmlquery-properties-hidden
		(if (not (memq 'mmlquery-property invis))
		    (setq invis (cons 'mmlquery-property invis) doit t))
	      (if (memq 'mmlquery-property invis)	      
		  (setq invis (delq 'mmlquery-property invis) doit t)))
	    (if doit (put-text-property (point) next-change 'invisible invis))))
      (goto-char next-change))))))


(defun mmlquery-find-abstract ()
"Start the Emacs MMLQuery browser for given article."
(interactive)
(or (file-directory-p mmlquery-abstracts)
    (error "MMLQuery abstracts not available, put them into %s, or change the variable 'mmlquery-abstracts!" mmlquery-abstracts))
(let ((olddir default-directory)
      (oldbuf (current-buffer)))
  (unwind-protect
      (progn 
	(cd mmlquery-abstracts)
	(call-interactively 'find-file))
    (set-buffer oldbuf)
    (cd olddir))))

;;;;;;;;;;;;;;;;;;;;; MoMM ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Caution, this version of mizar.el is transitory. I have
;; ported the Constr. Explanations to Mizar 6.2. here, but MoMM 0.2
;; is still based on Mizar 6.1, so in case you have Mizar 6.2, MoMM
;; will not work. I hope to port MoMM to Mizar 6.2. shortly. If you
;; want to use it in the meantime, use Mizar 6.1. and previous
;; version of mizar.el .


(defvar mizar-momm-compressed t
"*If t, the distribution files (except from the typ directory)
are gzipped to save space")

(defvar mizar-momm-max-start-time 20
"How long we wait for the MoMM process to start to exist;
loading can take longer, we just need the process")

(defvar mizar-momm-load-tptp t
"*If t, the simple justification clause bases are loaded into MoMM too.")

(defconst mizar-fname-regexp  "[A-Za-z0-9_]+"
"Allowed characters for mizar filenames.")

(defvar mizar-mommths (concat mizar-momm-dir "ths/")
  "Directory with articles' .ths files.")
(defvar mizar-mommtyp (concat mizar-momm-dir "typ/")
  "Directory with articles' .typ files.")
(defvar mizar-mommtptp (concat mizar-momm-dir "tptp/")
  "Directory with articles' .tptp files.")
(defvar mizar-mommall-tt (concat mizar-momm-dir "all.typ")
  "Complete type table to be loaded into MoMM.")
(defvar mizar-mommall-db (concat mizar-momm-dir "all.ths")
  "The MoMM database to load.
The .tb and .cb extensions will be appended to get
the termbank and clausebank.")
(defvar mizar-momm-binary (concat mizar-momm-dir "MoMM")
  "Path to the MoMM binary.")
(defvar mizar-momm-verifier (concat mizar-momm-dir "tptpver")
  "The verifier used for creating tptp problems.
They can be later sent to MoMM from unsuccessful simple justifications")
(defvar mizar-momm-exporter (concat mizar-momm-dir "tptpexp")
  "The exporter used for creating tptp problems form articles.
To be loaded into MoMM on  startup.")
(defvar mizar-relcprem (concat mizar-momm-dir "relcprem")
  "*The detector of irrelevant local constants, necessary for MoMM exporter.")

(defvar mizar-momm-rant "Please process clauses now, I beg you, great shining CSSCPA, wonder of the world, most beautiful program ever written.
"
  "The rant sequence to overcome CLIB input buffering.")

(defvar mizar-momm-finished (concat mizar-momm-rant " state: "
				    mizar-momm-rant)
  "The sequence to send at the end of initial data.
Used to get the 'loaded' response from MoMM.")

(defvar mizar-momm-accept-output t
"Used to suppress output during MoMM loading.")

(defvar mizar-momm-verbosity 'translate
"Possible values are now 'raw, 'translate.")


(defun mizar-toggle-momm ()
"Check that MoMM is installed first."
(interactive)
(if (and (not mizar-use-momm)
	 (not (file-executable-p mizar-momm-verifier)))
    (error "MoMM is not installed!"))
(setq mizar-use-momm (not mizar-use-momm)))

(defvar mizar-momm-err-map
  (let ((map (make-sparse-keymap))
	(button_kword (if (eq mizar-emacs 'xemacs) [(shift button3)]
			[(shift down-mouse-3)])))
    (set-keymap-parent map mizar-mode-map)
    (define-key map button_kword 'mizar-ask-momm)
    map)
"Keymap used at MoMM-sendable errors.")


(defconst directivenbr 8
"Tells how many kinds of directive there are (in .evl), see env_han.pas."
)
; Following is order of directives in .evl, see env_han.pas
(defconst voc-dir-order 0)
(defconst not-dir-order 1)
(defconst def-dir-order 2)
(defconst the-dir-order 3)
(defconst sch-dir-order 4)
(defconst clu-dir-order 5)
(defconst con-dir-order 6)
(defconst req-dir-order 7)

(defvar evl-table nil "The table of environment directives.")
(defvar evl-table-date -1
"Set to last accommodation date, after creating the table.
Used to keep tables up-to-date.")

(make-variable-buffer-local 'evl-table)
(make-variable-buffer-local 'evl-table-date)


(defun get-directive (directives start count)
"DIRECTIVES is a list created from .evl.
Get COUNT of them beginning at the START position."
  (let ((counter 0) (result ()))
    (while (< counter count)
      (setq result (append result (list (elt directives (+ start (* 2 counter))))))
      (setq counter (+ counter 1)))
    result))


(defun get-evl (aname)
"Return a `directivenbr'-long list of directives for the article ANAME.
Created from its .evl file."
(let ((evlname (concat aname ".evl")))
  (or (file-readable-p evlname)
	(error "File unreadable: %s, run accommodator first" evlname))
  (let ((evldate (cadr (nth 5 (file-attributes evlname)))))
    (if (/= evl-table-date evldate)
	(let ((decl (with-temp-buffer
		      (insert-file-contents evlname)
		      (split-string (buffer-string) "[\n]")))
	      (d ()) (i 0) (start 0) (count 0))
	  (while  (< i directivenbr)
	    (setq count (string-to-number (elt decl start)))
	    (setq d (append d (list (get-directive
				     decl (+ start 1) count))))
	    (setq start (+ start 1 (* 2 count)))
	    (setq i (+ 1 i)))
	  (setq  evl-table-date evldate
		 evl-table d)))
    evl-table)))

(defun get-theorem-dir (aname)
"Return list of theorem directives for ANAME."
  (elt (get-evl aname) the-dir-order))

(defun get-all-dirs (aname)
"Return list of all names occurring in some directive for ANAME."
(let ((d (get-evl aname))
      res (i 0))
  (while  (< i directivenbr)
    (setq res (append (elt d i) res)
	  i   (+ 1 i)))
  (unique res)))

(defun get-all-dirs-rec (aname)
  "Return list of all names occurring in some directive for ANAME,
plus transitive hull of constructors."
  (get-sgl-table aname)
  (unique (append cstrnames (get-all-dirs aname))))

(defun mizar-get-momm-input (aname pos)
"Search file ANAME.tptp for problems generated for given POS.
Return list of them."
(let* ((problems (concat aname ".tptp"))
       (linestr (number-to-string (car pos)))
       (colstr (number-to-string (cadr pos)))
       (searchstr (concat "^ninscheck: pos(" mizar-fname-regexp
			  ", 0, 0, " linestr ", " colstr ", .*"))
       res b e)
  (or (file-readable-p problems)
      (error "File %s not readable, run tptpver first!" problems))
  (with-temp-buffer
    (insert-file-contents problems)
    (goto-char (point-min))
    (while (re-search-forward searchstr (point-max) t)
      (setq b (match-beginning 0))
      (setq e (search-forward "." (point-max))) ; error if not found
      (setq res (cons (buffer-substring-no-properties b e) res))))
  (nreverse res)))

(defun mizar-ask-momm (event)
  "Ask MoMM for hints on an error at click EVENT.
The results are put into the buffer *MoMM's Hints*."
  (interactive "e")
  (select-window (event-window event))
  (save-excursion
    (let ((mommpr (get-process "MoMM"))
	  (pos (get-text-property (event-point event) 'pos)))
      (if (not mommpr) (error "Start MoMM first!"))
      (if (not pos) (error "No semantic error here, perhaps you did not run tptpver?"))
      (let ((in (mizar-get-momm-input
		 (file-name-sans-extension
		  (file-name-nondirectory (buffer-file-name)))
		 pos))
	    (cbuf (get-buffer-create "*MoMM's Hints*")))
	(if (not in)
	    (error "No data for MoMM found, use the right verifier!"))
	(set-buffer cbuf)
	(erase-buffer)
	(setq mizar-momm-accept-output t)
	(while in
	  (process-send-string mommpr (car in))
	  (process-send-string mommpr " ")
	  (process-send-string mommpr mizar-momm-rant)
	  (accept-process-output mommpr 2)
	  (setq in (cdr in)))
	(process-send-string mommpr mizar-momm-rant)
	(switch-to-buffer-other-window cbuf)
	(goto-char (event-point event))))))


(defun mizar-momm-hints-filter (res)
"Put the hints RES in buffer *MoMM's Hints* if `mizar-momm-accept-output'nonil.
Used to get rid of the output while MoMM loading."
(if (not mizar-momm-accept-output)
    (let ((l (length res)) (i 0))
      (while (< i l)
	(if (eq (aref res i) 35)      ; 35 = # - now serves as loaded-info
	    (setq mizar-momm-accept-output t
		  i l)
	  (setq i (+ 1 i))))))
(if mizar-momm-accept-output
    (let ((cbuf (get-buffer-create "*MoMM's Hints*")))
      (set-buffer cbuf)
      (cond
       ((string-match "^# CSSCPAState" res)  ; now serves as loaded-info
	(insert "MoMM loaded
")
	(message " ... MoMM loaded"))
       ((eq 'raw mizar-momm-verbosity)
	(insert res))
       ((string-match "^1" res)
	(insert "Tautology
"))
       ((string-match "^2" res)
	(insert "No match
"))
       ((string-match "^0" res)
	(insert "Unhandled by MoMM yet
"))
       ((string-match "^pos[(] *\\([^,]+\\), *\\([^,]+\\), *\\([^,]+\\), *\\([^,]+\\), *\\([^,]+\\)" res)
	(let ((type (match-string 2 res)))
	  (cond
	   ((string-equal "1" type)
	    (insert (concat (upcase (match-string 1 res))
			    ":" (match-string 3 res) "
")))
	   ((or (string-equal "2" type)    ; normal def theorem
		(string-equal "3" type)    ; func property
		(string-equal "4" type))   ; pred property
	    (insert (concat (upcase (match-string 1 res))
			    ":def " (match-string 3 res) "
")))
	   (t (insert (concat (match-string 0 res) ")
")))))))
       
      
;  (mizar-highlight-constrs)
;  (use-local-map mizar-cstr-map)
;  (goto-char (point-min))
;  (switch-to-buffer-other-window cbuf)))
)))

(defun mizar-momm-process-filter (proc str)
  (mizar-momm-hints-filter str))

(defun mizar-run-momm1 (typetables tlist &optional tb raw filter)
"Start MoMM  interactively in background.
If multiple TYPETABLES, they have to be appended into temporary file here.
TLIST is the list of files to load, TB is optional termbank.
If RAW is non-nil, process filter FILTER is used if given, otherwise none."
(interactive)
(if (get-process "MoMM") (kill-process "MoMM"))
(if (get-buffer "*MoMM*") (kill-buffer "*MoMM*"))
(sit-for 1)
(let* ((tt (cond
	    ((cdr typetables)     ; have to create tmp
	     (let ((temp (make-temp-name
		       (concat default-directory "tmptt")))
		 (t1 typetables))
	       (with-temp-file temp
		 (while t1
		   (insert-file-contents (car temp))
		  (setq t1 (cdr t1))))
	       temp))
	    (typetables (car typetables))
	    (t nil)))
       (args tlist) compr (i 0))
  (if mizar-momm-compressed
      (while args
	(if (equal (file-name-extension (car args)) "gz")
	    (setq compr (cons (car args) compr)
		  tlist (delete (car args) tlist)))
	(setq args (cdr args))))
  (setq mizar-momm-accept-output nil)
  (cond
   (compr
    (setq compr (concat "(gzip -dc "
			(mapconcat 'identity compr " ")
			"; cat)| ")
	  args (concat compr mizar-momm-binary " -s "
		       (if tt (concat " -y " tt " ") "")
		       (if tb (concat " -b " tb " ") "")
		       (if tlist (mapconcat 'identity tlist " ")
			 "")))
    (start-process-shell-command "MoMM" "*MoMM*" args))
   (t
    (setq args (append (list "MoMM" "*MoMM*" mizar-momm-binary "-s")
		       (if tt (list "-y" tt))
		       (if tb (list "-b" tb))
		       tlist (list "-")))
;  (apply 'make-comint args)
    (apply 'start-process args)))

  (while (and (not (get-process "MoMM"))
	      (< i mizar-momm-max-start-time))
    (sit-for 1)
    (setq i (+ 1 i)))
  (or (get-process "MoMM")
      (error "MoMM not started, try increasing mizar-momm-max-start-time"))
  (if raw
      (set-process-filter (get-process "MoMM") filter)
    (set-process-filter (get-process "MoMM")
			'mizar-momm-process-filter))
  (process-send-string (get-process "MoMM")
		       mizar-momm-finished)
  (if (cdr typetables)
      (message "Temporary typetable %s created" tt))
  (message "Loading MoMM data...")
))

(defun verify-file-readable (f)
  (or (file-readable-p f)
      (error "File %s not readable" f)))

(defun mizar-momm-get-default-files (aname &optional thsdirs tptp)
"Get default files for running MoMM for article ANAME.
Pair (not found, absolute names) is returned.
If THSDIRS is given, use instead of default.
TPTP tells to use tptp files too."
(let* ((args (if thsdirs (copy-alist (get-theorem-dir aname))
	       (get-all-dirs-rec aname)))
       res no f f1)
  (while args
    (setq f (concat mizar-mommths
		    (downcase (car args))
		    (if mizar-momm-compressed ".ths.cb.gz" ".ths.cb"))
	  f1 (concat mizar-mommtptp
		     (downcase (car args))
		     (if mizar-momm-compressed ".tptp.cb.gz"
		       ".tptp.cb")))
    (if (file-readable-p f) (setq res (cons f res))
      (setq no (cons f no)))
    (if tptp
	(if (file-readable-p f1)
	    (setq res (cons f1 res))
	  (setq no (cons f1 no))))
    (setq args (cdr args)))
  (list no (nreverse res))
))

(defun mizar-run-momm ()
"Get type, clause and termbank files for running MoMM and run it.
Default process filter is used.  Verify that the default argument
files exist first."
(interactive)
(let* ((aname (file-name-sans-extension
	       (file-name-nondirectory (buffer-file-name))))
       (args (cadr (mizar-momm-get-default-files aname nil
						 mizar-momm-load-tptp)))
       tt tb)
  (setq args (mapconcat 'identity args " "))
  (setq tts (split-string
	    (read-string  "Typetable(s): " mizar-mommall-tt)
	    "[, \f\t\n\r\v]+")
	args (split-string
	      (read-string  "Clause file(s): " args)
	      "[, \f\t\n\r\v]+")
	tb  (let ((s (read-string
		      "Termbank (Default: none): ")))
		(if (string-equal "" s) nil s)))
;  (mapcar 'verify-file-readable tts)
;  (mapcar 'verify-file-readable args)
;  (if tb (verify-file-readable tb))
  (mizar-run-momm1 tts args tb)))



(defun mizar-run-momm-default (&optional aname thsdirs tptp)
"Run MoMM for article ANAME.
Load theorems from all its directive filenames.
If THSDIRS is non-nil, use the theorem directive only.
Complete typetable is loaded, which makes later on demand
loading with `mizar-momm-add-files' possible.
Use TPTP to load the tptp files (non-theorem information) too."
(interactive)
(let* ((aname (or aname
		  (file-name-sans-extension
		   (file-name-nondirectory (buffer-file-name)))))
       (res (mizar-momm-get-default-files aname thsdirs tptp)))
  (mizar-run-momm1 (list mizar-mommall-tt) (cadr res))))


(defun mizar-run-momm-full ()
"Fast load MoMM with the full theorems db.
This takes about 120M in MoMM 0.2."
(interactive)
(mizar-run-momm1 (list mizar-mommall-tt)
		 (list (concat mizar-mommall-db ".cb"))
		 (concat mizar-mommall-db ".tb")))

(defun mizar-momm-get-file (f dir ext)
"Find the MoMM file F, possibly in DIR and with extension EXT."
(cond
 ((file-readable-p f) f)
 ((file-readable-p (concat f ext)) (concat f ext))
 ((file-readable-p (concat f ext ".cb")) (concat f ext ".cb"))
 ((and mizar-momm-compressed
       (file-readable-p (concat f ext ".cb.gz")))
  (concat f ext ".cb.gz"))
 ((file-readable-p (concat dir f)) (concat dir f))
 ((file-readable-p (concat dir f ext)) (concat dir f ext))
 ((file-readable-p (concat dir f ext ".cb")) (concat dir f ext ".cb"))
 ((and mizar-momm-compressed
       (file-readable-p (concat dir f ext ".cb.gz")))
  (concat dir f ext ".cb.gz"))
 (t nil)))

(defun mizar-momm-add-files (tlist &optional tptp)
  "Add ths files from TLIST into running MoMM.
The type-table must be loaded on start,
e.g. by running MoMM with all.typ.
If TPTP, load tptp files too.  Current directory is searched first,
then the MoMM db."
  (interactive "sarticles: ")
  (let ((mommpr (get-process "MoMM"))
	(tptp (or tptp mizar-momm-load-tptp))
	(i 0))
    (if (not mommpr) (error "Start MoMM first!"))
    (if (stringp tlist)
	(setq tlist (split-string tlist "[(), \f\t\n\r\v]+")))
    (setq mizar-momm-accept-output nil)
    (while tlist
      (let ((f (mizar-momm-get-file (car tlist) mizar-mommths ".ths"))
	    (f1 (if tptp
		    (mizar-momm-get-file  (car tlist)
					  mizar-mommtptp ".tptp"))))
	(if f
	    (with-temp-buffer
	      (if (and mizar-momm-compressed
		       (equal (file-name-extension f) "gz"))
		  (let ((excode (call-process "gzip" f t nil "-dc")))
		    (if (or (stringp excode) (/= 0 excode))
			(error "Error in decompressing %s" f)))
		(insert-file-contents f))
	      (process-send-string mommpr (buffer-string))
	      (setq i (+ 1 i))))
	(if (and f1 (not (equal f f1)))
	    (with-temp-buffer
	      (if (and mizar-momm-compressed
		       (equal (file-name-extension f1) "gz"))
		  (let ((excode (call-process "gzip" f1 t nil "-dc")))
		    (if (or (stringp excode) (/= 0 excode))
			(error "Error in decompressing %s" f1)))
		(insert-file-contents f1))
	      (process-send-string mommpr (buffer-string))
	      (setq i (+ 1 i))))
	(setq tlist (cdr tlist))))
    (message "Loading %d files ..." i)
    (process-send-string mommpr mizar-momm-finished)
    ))

(defun mizar-pos-at-point ()
  "Return the MoMM position at the point."
  (save-excursion
    (skip-chars-backward "^ \t\n,;")
    (if (looking-at "pos[(] *\\([^,]+\\), *\\([^,]+\\), *\\([^,]+\\), *\\([^,]+\\), *\\([^,]+\\)")
	(let ((article (match-string 1))
	      (line    (string-to-number (match-string 4)))
	      (col     (string-to-number (match-string 5))))
	  (list article line col)))))
      
(defun mizar-momm-find-pos ()
  "Find the position at point in other window."
(interactive)
(let ((pos (mizar-pos-at-point)))
  (if pos
      (let* ((line (cadr pos))
	     (col (car (last pos)))
	     (f1 (concat (car pos) ".miz"))
	     (f (if (file-readable-p f1) f1
		  (concat  mizar-mml "/" f1))))
	(save-excursion
	  (find-file-other-window f)
	  (set-buffer (get-file-buffer f))
	  (goto-line line)
	  (move-to-column (- col 1))))
  (message "No position at point"))))

;;;;;;;;;;;;;;;;;;;;; Mizar TWiki  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar mizar-twiki-url "http://wiki.mizar.org/cgi-bin/twiki/view/Mizar/")
(defvar mizar-twiki-questions (concat mizar-twiki-url "MizarQuestion"))
(defvar mizar-twiki-features (concat mizar-twiki-url "FeatureBrainstorming"))
(defvar mizar-twiki-language (concat mizar-twiki-url "MizarLanguage"))
(defvar mizar-twiki-pitfalls (concat mizar-twiki-url "MizarPitfalls"))
(defvar mizar-twiki-faq (concat mizar-twiki-url "MizarFAQ"))
(defvar mizar-twiki-bugs (concat mizar-twiki-url "BugReport"))
(defvar mizar-twiki-mml-sugg (concat mizar-twiki-url "MmlSuggestion"))

(defun mizar-error-at-point ()
  "Determine what error we're looking at right now."
  (let ((cw (current-word)))
    (if (string-match "[^0-9]*\\([0-9]+\\)\\b" cw)
	(match-string 1 cw)
      "")))

(defun mizar-twiki-comment-error (&optional errstr)
  "Add a comment to the Mizar TWiki description of an error message ERRSTR."
  (interactive)
  (let ((errstr
	 (or errstr
	     (read-string  (concat "ErrorCode to comment on: (Default: "
				   (mizar-error-at-point) "): " )
			   nil nil      (mizar-error-at-point)))))
    (browse-url (concat mizar-twiki-url "ErrorNo" errstr))))

;;;;;;;;;;;;;;;  abbrevs for article references ;;;;;;;;;;;;
(defun mizar-th-abbrevs (&optional aname)
  "Theorem abbrevs."
  (interactive)
  (let ((aname (or aname
		   (file-name-nondirectory
		    (file-name-sans-extension
		     (buffer-file-name))))))
    (setq aname (upcase aname))
    (save-excursion
      (goto-char (point-min))
      (let (pos0 pos1 comm (thnr 0) pairs)
	(while (re-search-forward "[ \n\r\t]\\(theorem\\)[ \n\r\t]+" (point-max) t)
	  (setq pos1 (point)
		pos0 (match-end 1))
	  (goto-char pos0)
	  (beginning-of-line)
	  (setq comm (search-forward comment-start pos0 t))
	  (if comm  (beginning-of-line 2)  ;; inside comment, skip
	    (setq thnr (+ thnr 1))
	    (goto-char pos1)               ;; label  or not
	    (if (looking-at "\\([a-zA-Z0-9_']+\\):")
		(define-abbrev mizar-mode-abbrev-table
		  (downcase (match-string 1))
		  (concat aname ":" (number-to-string thnr))))
;	  (setq pairs (cons (cons (match-string 1) thnr) pairs)))))
	    ))))))

(defun mizar-defs-abbrevs (&optional aname)
  (interactive)
  (let ((aname (or aname
		   (file-name-nondirectory
		    (file-name-sans-extension
		     (buffer-file-name))))))
    (setq aname (upcase aname))
    (save-excursion
      (goto-char (point-min))
      (let (pos0 pos1 comm (defnr 0) defname)
	(while (re-search-forward "[ \n\r\t]:\\([a-zA-Z0-9_']+\\):[ \n\r\t]" (point-max) t)
	  (setq pos0 (match-end 1)
		defname (match-string 1))
	  (goto-char pos0)
	  (beginning-of-line)
	  (setq comm (search-forward comment-start pos0 t))
	  (if comm  (beginning-of-line 2)  ;; inside comment, skip
	    (setq defnr (+ defnr 1))
	    (goto-char pos0)               ;; label  or not
	    (define-abbrev mizar-mode-abbrev-table
	      (downcase defname)
	      (concat aname ":def " (number-to-string defnr))))
	  )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; viewing constructor explanation of imported theorems and defs
(defvar theorem-table nil "Table of theorems for the article.")
(defvar theorem-directives nil "List of then directives parsed from thl.")
(defvar theorem-table-date -1
"As `constr-table-date'.")

(make-variable-buffer-local 'theorem-table)
(make-variable-buffer-local 'theorem-table-date)
(make-variable-buffer-local 'theorem-directives)


(defun parse-theorems (aname &optional reload)
"Load `theorem-table' and `theorem-directives' for ANAME.
Files .thl and .eth are used, RELOAD does it unconditionally."
(let ((thldate (cadr (nth 5 (file-attributes (concat aname ".thl"))))))
  (if (or reload (/= theorem-table-date thldate))
      (let (directives table)
      (with-temp-buffer
	(insert-file-contents (concat aname ".thl"))
	(let* ((all (split-string (buffer-string) "[\n]"))
	       (count (string-to-number (car all)))
	       (i 0))
	  (setq table (make-vector (* 2 count) 0)) ; just hash redundancy
	  (setq all (cdr all))
	  (while (< i count)
	    (let* ((symb (intern (car all) table))
		   (nrs (split-string (cadr all)))
		   (thvec (make-vector (string-to-number (car nrs))
				       nil))
		   (dfvec (make-vector (string-to-number (cadr nrs))
				       nil)))
	      (put symb 'ths thvec)
	      (put symb 'defs dfvec)
	      (setq directives (cons (car all) directives))
	      (setq i (+ 1 i))
	      (setq all (cddr all))))
	  (setq directives (nreverse directives)))
      (with-temp-buffer
	(insert-file-contents (concat aname ".eth"))
	(let* ((all (split-string (buffer-string) "[\n]"))
	       (count (string-to-number (car all)))
	       (dirs directives)
	       (i 0))
	  (setq all (cdr all))
	  (while (< i count)
	    (let* ((tcount (string-to-number (car all)))
		   (dcount 0)
		   (symb (intern-soft (car dirs) table))
		   (thvec (get symb 'ths ))
		   (dfvec (get symb 'defs))
		   (tnr 0) (dnr 0))
	      (setq all (cdr all))
	      (while (< tnr tcount)
		(aset thvec tnr (car all))
		(setq tnr (+ 1 tnr)
		      all (cddr all)))
	      (setq dcount (string-to-number (car all)))
	      (setq all (cdr all))
	      (while (< dnr dcount)
		(aset dfvec dnr (car all))
		(setq dnr (+ 1 dnr)
		      all (cddr all))))
	    (setq i (+ i 1)
		  all (cdr all)
		  dirs (cdr dirs))))))
      (setq theorem-table table
	    theorem-directives directives
	    theorem-table-date thldate)))
  theorem-table))

(defun mizar-ref-constrs (article nr &optional def table)
  "Constrs of the reference, if no table, use the buffer-local theorem-table.
Argument ARTICLE the article we're working on."
  (let* ((aname (file-name-nondirectory
		(file-name-sans-extension
		 (buffer-file-name))))
	 (ltable (or table (parse-theorems aname)))
	 (symb (intern-soft article ltable))
	 (what (if def 'defs 'ths))
	 arr res)
    (if (not symb) (error "Article %s not in theorem directives" article))
    (setq arr (get symb what))
    (if (< (length arr) nr)
	(error "Maximum for article %s is %d" article (length arr)))
    (get-sgl-table aname)           ;; ensure up-to-date
;    (parse-cluster-table aname)     ;; ensure up-to-date
    (setq res (copy-sequence (aref arr (- nr 1))))
    (mizar-transl-frm res)))

(defun mizar-show-ref-constrs (&optional ref)
"Get the constructors for reference REF (possibly reading from minibuffer).
Show them in the buffer *Constructors List*."
(interactive)
(let ((ref1 (or ref (read-string
		     (concat "Constructor explanation for: ("
			     (mizar-ref-at-point) "): ")
		     nil nil      (mizar-ref-at-point)))))
  (if (string-match "\\([a-z_0-9]+\\):\\(def\\)? *\\([0-9]+\\)" ref1)
      (mizar-intern-constrs-other-window
       (mizar-ref-constrs (match-string 1 ref1)
			  (string-to-number (match-string 3 ref1))
			  (match-string 2 ref1)))
    (error "Bad reference %s" ref1))
  ref1))

(defun mizar-mouse-ref-constrs (event)
"Show the constructors for reference at mouse EVENT."
  (interactive "e")
  (select-window (event-window event))
  (goto-char (event-point event))
  (mizar-show-ref-constrs (mizar-ref-at-point)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst mizar-error-regexp "\\(\\*\\|::>,\\)\\([0-9]+\\)" "Regexp used to locate error messages in a mizar text.")

(defvar mizar-region-count 0  "Number of regions on mizar-region-stack.")

(defvar mizar-imenu-expr
'(
  ("Reservations" "[ \n\r]\\(reserve\\b.*\\)" 1)
  ("Structures" "[ \n\r]\\(struct\\b.*\\)" 1)
  ("Modes" "[ \n\r]\\(mode\\b.*\\)" 1)
  ("Attributes" "[ \n\r]\\(attr\\b.*\\)" 1)
  ("Predicates" "[ \n\r]\\(pred\\b.*\\)" 1)
  ("Functors" "[ \n\r]\\(func\\b.*\\)" 1)
  ("Notations" "[ \n\r]\\(\\(synonym\\|antonym\\)\\b.*\\)" 1)
  ("Registrations" "[ \n\r]\\(\\(cluster\\|identify\\)\\b.*\\)" 1)
  ("Schemes" "^[ ]*scheme[ \n\r]+\\([a-zA-Z0-9_']+\\)" 1)
  ("Named Defs" "[ \n\r]\\(:[a-zA-Z0-9_']+:\\)[ \n\r]" 1)
  ("Named Theorems" "^[ ]*theorem[ \n\r]+\\([a-zA-Z0-9_']+:\\)[ \n\r]" 1)
)
"Mizar imenu expression.")


(defun toggle-quick-run ()
"Toggle the usage of quick-run for verifier, default is on."
(interactive)
(setq mizar-quick-run (not mizar-quick-run)))

(defun mizar-toggle-show-output (what)
"Set the size of the *mizar-output* window to WHAT.
See the documentation for the variable `mizar-show-output'."
(interactive)
(setq mizar-show-output what))

(defun mizar-toggle-goto-error (where)
"Set the error movement behavior after verifying to WHERE.
See the documentation for the variable `mizar-goto-error'."
(interactive)
(setq mizar-goto-error where))


(defun mizar-make-theorem-summary ()
  "Make a smmary of the theorems in the the current buffer.The
output will be put into a buffer called \"*Theorem-Summary*\"; if
that buffer already exists when this command is called, its
contents will be erased.

(The command `hs-hide-all', accessible from the Hide/Show menu,
can be used instead of `mizar-make-theorem-summary' to make a
summary of an article.)"
  (interactive)
  (message "Making theorem summary...")
  (setq result (mizar-make-theorems-string))
  (with-output-to-temp-buffer "*Theorem-Summary*"
    (save-excursion
      (let ((cur-mode "mizar"))
	(set-buffer standard-output)
	(mizar-mode)
	(erase-buffer)
	(insert result))
      (goto-char (point-min))))
  (message "Making theorem summary...done"))

(defun mizar-occur-refs ()
  "Generate an *Occur* buffer containing all references."
  (interactive)
  (occur "[ \\n\\r]by[ \\n\\r].*:"))


;;;;;;;;;;;;;;; Hiding items in abstracts ;;;;;;;;;;;;;;;;

(defgroup mizar-abstracts nil
  "Support for abstracts in the Mizar mode"
  :group 'mizar)

(defconst mizar-item-kinds
  '(theorem definition scheme registration notation reserve canceled)
"Top-level item kinds appearing in Mizar abstracts.
They are used as symbols for values of the overlay property 
'mizar-kind, and their names must correspond to the mizar keywords
introducing these items (see `mizar-set-item-overlays-in-abstract'.")

(defcustom mizar-abstracts-default-hidden-kinds nil
"*List of item kinds that get hidden upon loading of Mizar abstracts.
See `mizar-item-kinds' for possible values."
:type '(repeat symbol)
:group 'mizar-abstracts)

(defun mizar-abstracts-invisibility ()
  "Set up invisibility specs."
  (dolist (sym mizar-abstracts-default-hidden-kinds)
    (add-to-invisibility-spec sym)))

;; shouldn't this be done for items in `mizar-abstracts-default-hidden-kinds'?
;; No: this does not hide anything, only sets the overlays and gives
;;     their 'invisibility property the proper "kind" value; the hiding is
;;     then done (if user wants) by `mizar-abs-toggle-hiding', by moving
;;     the particular "kind" value to `buffer-invisibility-spec'
(defun mizar-set-item-overlays-in-abstract ()
  "Set the overlays for invisibility of items in a Mizar abstract.
This is done for items from `mizar-item-kinds'."
  (if (buffer-abstract-p (current-buffer))
      (save-excursion
	(let ((kinds mizar-item-kinds))
;;	(let ((kinds mizar-abstracts-default-hidden-kinds))
	  (while kinds
	    (let* ((kind (car kinds))
		   (kw (symbol-name kind))
		   (re (concat "^[ ]*" kw "[ \n\r]+" 
			       (if (memq kind 
					 '(definition registration notation))
				   "\\([\n\r]\\|.\\)*?\\bend\\b[; \n\r]+" 
				 "[^;]+;[ \n\r]+"))))
	      (goto-char (point-min))
	      (while
		  (re-search-forward re (point-max) t)
		(let* ((from (match-beginning 0))
		       (to (match-end 0)) 
		       (overlay (make-overlay from to)))
		  (overlay-put overlay 'invisible kind)
		  (overlay-put overlay 'mizar-kind kind)
		  (overlay-put overlay 
			       'isearch-open-invisible-temporary t))))
	    (setq kinds (cdr kinds)))))
    (error "Not currently in Mizar abstract!")))

(defun mizar-abs-toggle-hiding (sym)
  "Toggle hiding of symbol SYM in abstracts."
  (unless (buffer-abstract-p (current-buffer))
    (error "Not currently in Mizar abstract!"))
  (if (and (listp buffer-invisibility-spec)
	   (memq sym buffer-invisibility-spec))
      (remove-from-invisibility-spec sym)
    (add-to-invisibility-spec sym))
  (redraw-frame (selected-frame))   ; Seems needed
  )

(defun mizar-abs-toggle-th ()
  "Toggle hiding of theorems in abstracts."
  (interactive)
  (mizar-abs-toggle-hiding 'theorem))

(defun mizar-abs-toggle-def ()
  "Toggle hiding of definitions in abstracts."
  (interactive)
  (mizar-abs-toggle-hiding 'definition))

(defun mizar-abs-toggle-sch ()
  "Toggle hiding of schemes in abstracts."
  (interactive)
  (mizar-abs-toggle-hiding 'scheme))

(defun mizar-abs-toggle-reg ()
  "Toggle hiding of registrations in abstracts."
  (interactive)
  (mizar-abs-toggle-hiding 'registration))

(defun mizar-abs-toggle-not ()
  "Toggle hiding of notations in abstracts."
  (interactive)
  (mizar-abs-toggle-hiding 'notation))

(defun mizar-abs-toggle-res ()
  "Toggle hiding of reservations in abstracts."
  (interactive)
  (mizar-abs-toggle-hiding 'reserve))

(defun mizar-abs-toggle-can ()
  "Toggle hiding of canceled items in abstracts."
  (interactive)
  (mizar-abs-toggle-hiding 'canceled))

;;;;;;;;;;;;;;; Verifier mode line ;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar verifier-mode nil
  "True if verifier mode is in use.")

(add-to-list 'minor-mode-alist '(verifier-mode verifier-mode))
(make-variable-buffer-local 'verifier-mode)
(put '-mode 'permanent-local t)

(defun verifier-mode ()
  ;; Dummy function for C-h m
  "Mizar Verifier minor mode.
This minor mode is automatically activated whenever 
you verify a Mizar file.")

(defun verifier-mode-line (error-nr)
  "Set variable `verifier-mode' to display verification report.
ERROR-NR is reported in current buffer's mode line."
  (interactive)
  (setq verifier-mode (concat " " "Errors:" (number-to-string error-nr)))
  (force-mode-line-update))

;;;;;;;;;;;;;;;; Running Mizar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun mizar-new-term-output (&optional force)
"Prepare output buffer if it was destroyed by quick-run; 
if FORCE is non nil, do this no matter what the value of `mizar-quick-run'"
(if (or force (not mizar-quick-run))
    (let ((buff (get-buffer "*mizar-output*"))
	  (dir default-directory))
      (if (and  buff
		(not (member '(major-mode . term-mode)
			     (buffer-local-variables buff))))
	  (progn (kill-buffer buff) (setq buff nil)))
      (if (not buff)
	  (save-window-excursion
	    (ansi-term "bash")
	    (rename-buffer "*mizar-output*")))
      (display-buffer "*mizar-output*")
      (save-excursion
	(set-buffer "*mizar-output*")
	(cd  dir))
      (end-of-buffer-other-window 0))))


(defun mizar-compile (&optional util)
"Run verifier (`mizar-it') in a compilation-like way.
This means that the errors are shown and clickable in buffer 
*Compilation*, instead of being put into the editing buffer in
the traditional Mizar way.
If UTIL is given, call it instead of the Mizar verifier."
  (interactive)
  (mizar-it util nil t))

; (defun mizar-compile ()
;   "compile a mizar file in the traditional way"
;   (interactive)
;   (let ((old-dir (mizar-switch-to-ld)))
;     (compile (concat "mizfe " (substring (buffer-file-name) 0 (string-match "\\.miz$" (buffer-file-name)))))
;     (if old-dir (setq default-directory old-dir))))



(defun mizar-handle-output  ()
"Display processing output according to `mizar-show-output'."
(cond ((eq 'none mizar-show-output)
       (delete-other-windows))
      ((integerp mizar-show-output)
       (save-selected-window
; get-buffer-window seems buggy in winemacs
;		   (select-window (get-buffer-window
	 (pop-to-buffer
	  (get-buffer "*mizar-output*"))
	 (goto-char (point-max))
	 (delete-blank-lines)
	 (let ((new-height 
		(min mizar-show-output
		     (max window-min-height ;; prevent deleting
			  (count-lines (point-min) (point-max))))))
; no sense winemacs behaves strange anyway
;	   (if (fboundp 'set-window-text-height)
;	       (set-window-text-height (get-buffer-window (current-buffer))
;				       new-height)
	   (shrink-window (- (window-height) (+ 1 new-height)))
	   (goto-char (point-max))
	   (forward-line (- new-height))
	   (set-window-start (get-buffer-window (current-buffer)) (point))
	   )))
      (t
       (save-selected-window
	 (pop-to-buffer
	  (get-buffer "*mizar-output*"))))))

(defun mizar-show-errors ()
  "Post processing error explanation."
  (let ((pos (point)))
    (cond ((equal "first" mizar-goto-error)
	   (goto-char (point-min))
	   (if (not (mizar-next-error))
	       (goto-char pos)))
	  ((equal "next" mizar-goto-error)
	   (mizar-next-error))
	  ((equal "previous" mizar-goto-error)
	   (mizar-previous-error))
	  (t pos))))

(defcustom mizar-forbid-accommodation nil
"*The Mizar accomodator is not called under any circumstances.
This is used for teaching purposes, when the article environment
was produced by the teacher, and it is not desirable that the 
students experimented with accommodating.
Normal users should not change this option."
:type 'boolean
:group 'mizar-education)

(defun mizar-call-util (program &optional buffer &rest args)
"Wrapper around `call-process', handling mizar options.
Currently only `mizar-allow-long-lines'."
(if mizar-allow-long-lines
    (apply 'call-process program nil buffer nil "-l" args)
  (apply 'call-process program nil buffer nil args)))

(defun mizar-accom (accomname force buffer article)
(if mizar-forbid-accommodation 0
  (if force (mizar-call-util accomname buffer "-a" article)
    (mizar-call-util accomname buffer article))))

(defun mizar-noqr-sentinel (process signal)
  (if (memq (process-status process) '(exit signal))
      (mizar-handle-noqr-exit (car mizar-noqr-data))))

(defvar mizar-noqr-data nil
  "Holds the filename of the mizar article currently processed using 
`term-exec', and the associated process (i.e. it is a cons cell
\(filename . process). 
Nil iff nothing is processed right now, serves also as a state variable.")

(defun mizar-handle-noqr-exit (filename)  
(setq mizar-noqr-data nil)
(let* ((name (file-name-sans-extension filename))
       (fname (file-name-nondirectory name)))
  (pop-to-buffer (get-file-buffer filename))
  (if mizar-do-expl
      (save-excursion
	(remove-text-properties (point-min) (point-max)
				'(mouse-face nil expl nil local-map nil))
	(mizar-put-bys fname)))	     
  (mizar-do-errors name)
  (save-buffer)
  (mizar-handle-output)
  (mizar-show-errors))
)

(defun mizar-buf-verifiable-p (&optional buffer)
"Simple check if verifier can be run on BUFFER."
(string-match "[.]miz$" (buffer-file-name buffer)))

(defun mizar-it-noqr (&optional options util forceacc)
"Run mizar in terminal on the text in the current .miz buffer.
Show the result in buffer *mizar-output*.
If OPTIONS are given, pass them to the verifier.
If UTIL is given, run it instead of verifier.
If `mizar-use-momm', run tptpver instead.
If FORCEACC, run makeenv with the -a option."
  (interactive)
  (let ((util (or util (if mizar-use-momm mizar-momm-verifier
			 mizar-verifier)))
	(makeenv makeenv))
    (if (eq mizar-emacs 'winemacs)
	(progn
	  (setq util (concat mizfiles util)
		makeenv (concat mizfiles makeenv))))
    (cond ((not (string-match "miz$" (buffer-file-name)))
	   (error "Not currently in .miz file!!"))
	  ((and (not mizar-forbid-accommodation)
		(not (executable-find makeenv)))
	   (error (concat makeenv " not found or not executable!!")))
	  ((not (executable-find util))
	   (error (concat util " not found or not executable!!")))
	  (t
	   (let* ((filename (buffer-file-name))
		  (name (file-name-sans-extension (buffer-file-name)))
		  (fname (file-name-nondirectory name))
		  (old-dir (file-name-directory name)))
	     (cd (concat old-dir ".."))
	     (if mizar-noqr-data (kill-process (cdr mizar-noqr-data)))
	     ;; now mizar-noqr-data is nil, it was cleared by the handler
	     (if mizar-noqr-data (error "Previous process unkillable"))
	     (mizar-strip-errors)
	     (save-buffer)
	     (unwind-protect
		 (let  ((excode (mizar-accom makeenv forceacc nil name)))
		   (if (and (numberp excode) (= 0 excode))
		       (progn
			 (mizar-new-term-output noqr)
			 (term-exec "*mizar-output*" util util nil 
				    (if options (list name options)
				      (list name)))
			 (let ((proc (get-buffer-process "*mizar-output*")))
			   (setq mizar-noqr-data (cons filename proc))
			   (set-process-sentinel proc 'mizar-noqr-sentinel))
			 )
		     (mizar-handle-noqr-exit filename)))
	       (if old-dir (setq default-directory old-dir)))
	     )))))

(defvar last-verification-date '(-1 -1)
"Set to the date of last verification.
Needed e.g. for determining if the .xml files are 
in sync with .miz, because the .miz file is usually 
modified with errors right after the verification 
(and hence slightly newer than the .xml file).")

(make-variable-buffer-local 'last-verification-date)

(defun mizar-it (&optional util noqr compil silent forceacc options)
"Run mizar verifier on the text in the current .miz buffer.
Show the result in buffer *mizar-output*.
In interactive use, a prefix argument directs this command
to read verifier options from the minibuffer.

If OPTIONS are given, pass them to the verifier.
If UTIL is given, run it instead of verifier.
If `mizar-use-momm', run tptpver instead.
If NOQR, does not use quick run.
If COMPIL, emulate compilation-like behavior for error messages.
If SILENT, just run UTIL without messaging and errorflagging.
If FORCEACC, run makeenv with the -a option."
  (interactive (if current-prefix-arg
		   (list nil nil nil nil nil 
			 (read-string "Verifier options: "))))
  (if (or noqr (not mizar-quick-run)) 
      (mizar-it-noqr options util forceacc)
  (let ((util (or util (if mizar-use-momm mizar-momm-verifier
			 mizar-verifier)))
	(makeenv makeenv)
	(options (or options "")))
    (if (eq mizar-emacs 'winemacs)
	(progn
	  (setq util (concat mizfiles util)
		makeenv (concat mizfiles makeenv))))
    (cond ((not (string-match "miz$" (buffer-file-name)))
	   (error "Not currently in .miz file!!"))
	  ((and (not mizar-forbid-accommodation)
		(not (executable-find makeenv)))
	   (error (concat makeenv " not found or not executable!!")))
	  ((not (executable-find util))
	   (error (concat util " not found or not executable!!")))
	  (t
	   (let* ((name (file-name-sans-extension (buffer-file-name)))
		  (fname (file-name-nondirectory name))
		  (old-dir (file-name-directory name)))
	     (cd (concat old-dir ".."))
;;	     (if mizar-launch-dir (cd mizar-launch-dir))
	     (unless silent (mizar-strip-errors))
	     (save-buffer)
	     (unwind-protect
		 (cond
		  (silent 
		   (let ((excode (mizar-accom makeenv forceacc nil name)))
		     (if (and (numberp excode) (= 0 excode))
			 (mizar-call-util util nil "-q" name)
		       (error "Makeenv error, try mizaring first!"))))
		  (compil
		   (if (get-buffer "*compilation*") ; to have launch-dir
		       (kill-buffer "*compilation*"))
		   (let ((cbuf (get-buffer-create "*compilation*")))
		     (switch-to-buffer-other-window cbuf)
		     (erase-buffer)
		     (insert "Running " util " on " fname " ...\n")
		     (sit-for 0)	; force redisplay
					; call-process can return string (signal-description)
		     (let ((excode (mizar-accom makeenv forceacc cbuf name)))
		       (if (and (numberp excode) (= 0 excode))
			   (mizar-call-util util cbuf "-q" name)))
		     (other-window 1)))
		  (t
		   (save-excursion
		     (message (concat "Running " util " on " fname " ..."))
		     (if (get-buffer "*mizar-output*")
			 (progn 
			   (if (get-buffer-window "*mizar-output*")
			       (delete-window (get-buffer-window "*mizar-output*")))
			   (kill-buffer "*mizar-output*")))
		     (let* ((mizout (get-buffer-create "*mizar-output*"))
			    (excode (mizar-accom makeenv forceacc mizout name)))
		       (if (and (numberp excode) (= 0 excode))
			   (shell-command (concat 
					   util (if mizar-allow-long-lines " -q -l " 
						  " -q ") options " "
						  (shell-quote-argument name))
					  mizout)
			 (display-buffer mizout)))
		     (message " ... done"))))
	       (if old-dir (setq default-directory old-dir))
	       (unless silent
		 (if mizar-do-expl
		     (save-excursion
		       (remove-text-properties 
			(point-min) (point-max)
			'(mouse-face nil expl nil local-map nil))
		       (mizar-put-bys fname)))
		 (if compil
		     (save-excursion
		       (set-buffer "*compilation*")
		       (insert (mizar-compile-errors name))
		       (compilation-mode)
		       (goto-char (point-min)))
		   (mizar-bubble-ref-region (point-min) (point-max))
		   (mizar-do-errors name)
		   (save-buffer)
		   (setq last-verification-date (file-mtime (buffer-file-name)))
		   (mizar-handle-output)
		   (mizar-show-errors)))
	       )))))))

(defun mizar-it-parallel ()
"Call the mizp.pl parallel verifier on the article.
Only usable on systems with Perl and libxml installed."
  (interactive)
(mizar-it "mizp.pl" nil nil nil nil mizar-parallel-options))

(defun mizar-irrths ()
"Call Irrelevant Theorems & Schemes Detector on the article."
  (interactive)
(mizar-it "irrths" nil nil nil t))

(defun mizar-irrvoc ()
"Call Irrelevant vocabulary Detector on the article."
  (interactive)
(mizar-it "irrvoc" nil nil nil t))

(defun mizar-inacc ()
"Call Inaccessible Items Detector on the article."
  (interactive)
(mizar-it "inacc"))

(defun mizar-relinfer ()
"Call Irrelevant Inferences Detector on the article."
  (interactive)
(mizar-it "relinfer"))

(defun mizar-relprem ()
"Call Irrelevant Premises Detector on the article."
  (interactive)
(mizar-it "relprem"))

(defun mizar-reliters ()
"Call Irrelevant Iterative Steps Detector on the article."
  (interactive)
(mizar-it "reliters"))

(defun mizar-trivdemo ()
"Call Trivial Proofs Detector on the article."
  (interactive)
(mizar-it "trivdemo"))

(defun mizar-chklab ()
"Call Irrelevant Label Detector on the article."
  (interactive)
(mizar-it "chklab"))



(defun mizar-findvoc ()
  "Find vocabulary for a symbol."
  (interactive)
  (shell-command (concat "findvoc "
			 (read-string  (concat "findvoc [-iswGKLMORUV] SearchString (Default: " (current-word) "): " )
				       nil nil      (current-word))
			 )))
(defvar mizar-irr-utils 
'("relprem" "relinfer" "reliters" "chklab" "inacc" "trivdemo")
"Sequence of irrelevant utilities used in `mizar-run-all-irr-utils'.")

(defun mizar-run-all-irr-utils ()
"Run all the irrelevant utilities, stopping on the first error.
See the variable `mizar-irr-utils' for their list and order of execution."
(interactive)
(let ((utils mizar-irr-utils)
      (name (file-name-sans-extension (buffer-file-name)))
      err)
  (while (and utils (null err))
    (progn
      (mizar-it (car utils) nil nil nil t)
      (setq err (mizar-err-codes name)
	    utils (cdr utils))))))


;;;;;;;;;;;; not done yet, seems quite complicated if we have e.g.
;;;;;;;;;;;; reserve A for set reserve F for Function of A,B
; (defun mizar-show-type (&optional whole-exp)
;   "show last type reserved for a variable"
;   (interactive "p")
;   (save-excursion
;     (setq var (read-string  (concat "reserved type of (Default: " (current-word) "): " )
; 				       nil nil      (current-word)))
;     (while
;  	(and
; 	 (re-search-backward "^ *reserve" (point-min) t)
; 	 (setq pos (match-beginning 0))
; 	 (re-search-forward (concat "[, \n]" var "[, \n]") " *\\([;]\\|by\\|proof\\)" (point-max) t))

(defun mizar-make-reserve-summary ()
  "Make a summary of all type reservations before current point in the article.
Display it in the `*Occur*' buffer, which uses the `occur-mode'.
Previous contents of that buffer are killed first.
Useful for finding out the exact meaning of variables used in
some Mizar theorem or definition."
  (interactive)
  (let* ((old-face (if (boundp 'list-matching-lines-face)
		       list-matching-lines-face)))
    (if (get-buffer "*Occur*") (kill-buffer "*Occur*"))
    (unwind-protect
	(save-restriction
	  (narrow-to-region (point-min) (point))
	  ;; prevent occur from messing Mizar faces
	  (if old-face
	      (setq list-matching-lines-face nil))
	  (occur "\\breserve\\b[^;]+;")
	  (if (get-buffer "*Occur*")
	      (message "Showing reservations before point")
	    (message "No reservations before point")))
      (if old-face
	  (setq list-matching-lines-face old-face)))))

(defun mizar-listvoc ()
  "List vocabulary."
  (interactive)
  (shell-command (concat "listvoc "
			 (read-string  (concat "listvoc  VocNames (Default: " (current-word) "): " )
				       nil nil      (current-word))
			 )))

(defun mizar-constr ()
"Show required constructors files.
Constructor files needed for Mizar theorems, definitions, 
schemes or complete articles can be queried."
  (interactive)
  (shell-command (concat "constr "
			 (read-string  (concat "constr [-f FileName] Article:[def|sch|...] Number (Default: " (mizar-ref-at-point) "): " )
				       nil nil      (mizar-ref-at-point))
			 )))

(defvar mizar-error-start "^::>")
(defvar mizar-error-start-length 3)

(defun mizar-end-error (result pos oldpos &optional prev)
  "Common end for mizar-next-error and mizar-previous-error."
  (if result
      (let ((find (concat "^::>[ \t]*\\(" result ":.*\\)[ \t]*$")))
	(goto-char (point-max))
	(re-search-backward find (point-min) t)
	(message (match-string 1))
	(goto-char pos))
    (goto-char oldpos)
    (ding)
    (message (concat "No more errors "
		     (if prev "above!!"  "below!!")))
    nil ))

(defun mizar-next-error ()
"Go to the next error in a mizar text, return nil if not found.
Show the error explanation in the minibuffer."
  (interactive)
  (let ((oldpos (point))
	(inerrl nil) ;; tells if we start from an error line
	result pos)
    (beginning-of-line)
    (if (looking-at (concat mizar-error-start "[^:\n]+$"))
	(progn
	  (forward-char mizar-error-start-length)  ;; skip the error start
	  (if (< (point) oldpos)     ;; we were on an error or between
	      (progn
		(goto-char oldpos)
		(if (looking-at "[0-9]+") ;; on error
		    (forward-word 1))))
	  (skip-chars-forward "\t ,*")  ;; now next error or eoln
	  (if (looking-at "[0-9]+")
	    (setq pos (point) result (match-string 0)))))
    (if (and (not result)
	     (re-search-forward (concat mizar-error-start "[^:\n]+$") 
				(point-max) t)) ;; to avoid bottom explanations
	(progn
	  (beginning-of-line)
	  (forward-char mizar-error-start-length)
	  (skip-chars-forward "\t ,*")
	  (if (looking-at "[0-9]+")
	    (setq pos (point) result (match-string 0)))))
    (mizar-end-error result pos oldpos)))

(defun mizar-previous-error ()
"Go to the previous error in a mizar text, return nil if not found.
Show the error explanation in the minibuffer."
  (interactive)
  (let ((oldpos (point))
	(inerrl nil) ;; tells if we start from an error line
	result pos)
    (beginning-of-line)
    (if (looking-at (concat mizar-error-start "[^:\n]+$"))
	(progn
	  (end-of-line)
	  (if (> (point) oldpos)     ;; we were on an error or between
	      (progn
		(goto-char oldpos)
		(if (looking-at "[0-9]+") ;; on error
		    (skip-chars-backward "0-9"))))
	  (skip-chars-backward "\t ,*") ; whitechars
	  (skip-chars-backward "0-9") ; startof err if any
	  (if (looking-at "[0-9]+") ; another on ths line
	      (setq pos (point) result (match-string 0))
	    (beginning-of-line))))  ; nothing else here
    (if (and (not result)
	     (re-search-backward (concat mizar-error-start "[^:\n]+$")  
				 (point-min) t))
	(progn
	  (end-of-line)
	  (forward-word -1)
	  (if (looking-at "[0-9]+")
	    (setq pos (point) result (match-string 0)))))
    (mizar-end-error result pos oldpos t)))
    
(defun mizar-strip-errors ()
  "Delete all error lines added by Mizar.
These are lines beginning with ::>."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^::>.*\n" nil t)
      (replace-match "" nil nil))
    ))


(defun mizar-show-environ ()
"*Show the environment part of the current article in other window.
Use for convenient editing of article's environment directives."
(interactive)
(switch-to-buffer-other-window (current-buffer))
(goto-char (point-min))
(unless (re-search-forward "\\benviron\\b" (point-max) t)
  (error "Current buffer has no environment part!"))
(set-window-start (get-buffer-window (current-buffer)) (point)) )


(defun mizar-hide-proofs (&optional beg end remove)
  "Put @@ before all proof keywords between BEG and END to disable checking.
With prefix (which makes REMOVE non-nil) remove them 
instead of adding, to enable proof checking again."
  (interactive "r\nP")
  (save-excursion
    (let ((beg (or beg (point-min)))
	  (end (or end (point-max))))
    (goto-char beg)
    (message "(un)hiding proofs ...")
    (if remove
	(while (re-search-forward "@proof\\b" end  t)
	  (replace-match "proof" nil nil))
      (while (re-search-forward "\\bproof\\b" end t)
	(replace-match "@proof" nil nil)))
    (message "... Done")
    )))

(defun mizar-move-then (&optional beg end reverse)
"Change the placement of the 'then' keyword between BEG and END.
With prefix (REVERSE non-nil) move from the end of lines to beginnings,
otherwise from beginnings of lines to ends.
This is a flamewar-resolving hack."
  (interactive "r\nP")
  (save-excursion
    (let ((beg (or beg (point-min)))
	  (end (or end (point-max))))
    (goto-char beg)
    (message "moving then ...")
    (if reverse
	(while (re-search-forward "; *\n\\( *\\)then " end t)
	  (replace-match "; then\n\\1 " nil nil))
      (while (re-search-forward "; *then *[\n]\\( *\\)" end  t)
	(replace-match ";\n\\1then " nil nil)))
    (message "... Done")
    )))



(defun mizar-make-theorems-string ()
  "Make string of all theorems."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (setq result "")
    (while
 	(and
	 (re-search-forward "^ *\\(theorem[^s]\\)" (point-max) t)
	 (setq pos (match-beginning 1))
	 (re-search-forward " *\\([;]\\|by\\|proof\\)" (point-max) t))
      (progn
	(setq result1 (buffer-substring-no-properties pos (match-beginning 0)))
	 (if  (string-match "\n$" result1)
	     (setq result (concat result result1 "\n" ))
	   (setq result (concat result result1 "\n\n" )))))
    result))

;; Abbrevs
(setq dabbrev-abbrev-skip-leading-regexp "\\(\\sw+\\.\\)+" )

(defun mizar-fnt-regexp (words)
"Create the regexp for font-lock from list of words WORDS."
(concat "\\<\\b\\(" (mapconcat 'identity words "\\|") "\\)\\b"))

;; Font lock
(defvar mizar-symbol-color nil "The color for the optional symbol fontification, white is suggested for the light-bg, nil (default) means no symbol fontification is done.")


(defun mizar-font-lock-keywords ()
  "Set up font lock keywords for the current Mizar system."
  (require 'font-lock)
  (if (boundp 'font-lock-background-mode)
      ()
    (make-local-variable 'font-lock-background-mode)
    (setq font-lock-background-mode 'light)) ; Assume light bg
  (if (boundp 'font-lock-display-type)
      ()
    (make-local-variable 'font-lock-display-type)
    (setq font-lock-display-type 'color)) ; Assume color

  ;; Create faces
  ;; Format: (FACE FOREGROUND BACKGROUND BOLD-P ITALIC-P UNDERLINE-P)
  (let* ((dark-bg (eq font-lock-background-mode 'dark))
	 (faces
	  (cond
	   ((memq font-lock-display-type 
		  '(mono monochrome grayscale greyscale grayshade 
			 greyshade))
	    `((mizar-main-face  nil nil nil nil t)
	      (mizar-block-face nil nil nil nil t)
	      (mizar-normal-face nil nil nil nil t)
	      (mizar-formula-face nil nil nil nil t)
	      (mizar-skeleton-face  nil nil nil nil t)
	      ;;		    (mizar-symbol-face nil nil nil nil t)
	      ))
	   (t				; light colour background
	    `(
	      (mizar-main-face ,mizar-main-color  nil nil nil nil)
	      (mizar-block-face ,mizar-block-color nil nil nil nil)
	      (mizar-normal-face ,mizar-normal-color nil nil nil nil)
	      (mizar-formula-face ,mizar-formula-color nil nil nil nil)
	      (mizar-skeleton-face ,mizar-skeleton-color nil nil nil nil)
;;            (mizar-symbol-face mizar-symbol-color nil nil nil nil)
	      )))))
    ;; mizar-symbol-color fontification
    (if mizar-symbol-color
	(setq faces (cons (list 'mizar-symbol-face mizar-symbol-color nil nil nil nil) faces)))

    (while faces
      (if (fboundp 'font-lock-make-face)
	  ;; The preferred way
	  (font-lock-make-face (car faces))
	;; The clumsy way
	(let ((facename (nth 0 (car faces)))
	      (fg (nth 1 (car faces)))
	      (bg (nth 2 (car faces)))
	      (bold (nth 3 (car faces)))
	      (ital (nth 4 (car faces)))
	      (under (nth 5 (car faces))))
	  (make-face facename)
	  (if fg (set-face-foreground facename fg))
	  (if bg (set-face-background facename bg))
	  (if bold (make-face-bold facename))
	  (if ital (make-face-italic facename))
	  (if bold (make-face-bold facename))
	  (set-face-underline-p facename under)
	  ;; This is needed under Emacs 20 for some reason.
	  (set facename facename)
	  ))
      (setq faces (cdr faces))))
      
  ;; Font Lock Patterns
  (let (
	;; "Native" Mizar patterns
	(head-predicates 
	 (list (mizar-fnt-regexp 
		(append mizar-main-keywords mizar-environment-keywords))
	       0 'mizar-main-face))
	(connectives
	 (list (mizar-fnt-regexp mizar-formula-keywords)
	   ;;		 1 font-lock-variable-name-face
	   1 'mizar-formula-face))
	(proofs
	 (list (mizar-fnt-regexp mizar-block-keywords)
	   0 'mizar-block-face ))
	(comments '("::[^\n]*"  0 'font-lock-comment-face ))
	(refs '("[ \n\t]\\(by\\|from\\)[^;.]*" 0 'font-lock-type-face))	
	(extra '("&"  0  'mizar-formula-face))
	(keywords			; directives (queries)
	 (list (mizar-fnt-regexp mizar-normal-keywords)
	  ;;		1 'mizar-formula-face
	  1 'mizar-normal-face))
	(skeletons 
	 (list (mizar-fnt-regexp mizar-skeleton-keywords)
	       0  'mizar-skeleton-face))
	(syms
	 (if mizar-symbol-color
	     (list (mizar-get-dct (file-name-sans-extension (buffer-file-name)))
		   0 'mizar-symbol-face)))
	)
    ;; Make font lock list
    (delq
     nil
     (cond
      ((eq major-mode 'mizar-mode)
       (list
	comments
	extra
	refs
	head-predicates
	connectives
	proofs
	keywords
	skeletons
	;; only if mizar-symbol-color defined and article has .dct
	(if (and syms (not (equal "" (car syms)))) syms)
	))
))
    ))

(defcustom mizar-mode-hook nil
  "A hook for Mizar mode."
  :type 'hook
  :group 'mizar)

(defun mizar-mode (&optional arg)
  "Major mode for editing Mizar articles and viewing Mizar abstracts.

In addition to the following commands, there are special bindings
for special buffers *Constructors list* and *MML Query Input*.
See the documentation for variables `mizar-cstr-map' and `query-entry-map'
for more.

Commands:
\\{mizar-mode-map}
Entry to this mode calls the value of `mizar-mode-hook'
if that value is non-nil."
  (interactive "P")
  (kill-all-local-variables)
  (use-local-map mizar-mode-map)
  (setq major-mode 'mizar-mode)
  (setq mode-name "Mizar")
  (setq local-abbrev-table mizar-mode-abbrev-table)
  (mizar-mode-variables)
  (setq buffer-offer-save t)
  (mizar-setup-imenu-sb)
  (if (buffer-abstract-p (current-buffer))
      (mizar-set-item-overlays-in-abstract))
  (if (and mizar-abstracts-use-view
	   (buffer-abstract-p (current-buffer)))
      (view-mode))
  (add-to-list 'fontification-functions 'mizar-underline-cexpls)
  (make-local-variable 'font-lock-fontify-region-function)
  (let ((oldfun font-lock-fontify-region-function))
    (setq font-lock-fontify-region-function
	  `(lambda (beg end loudly) 
	     (,oldfun beg end loudly)
	     (mizar-underline-in-region beg end))))

  (mizar-bubble-ref-region (point-min) (point-max))
  (run-hooks 'mizar-mode-hook)
  )

(defvar html-help-url "http://ktilinux.ms.mff.cuni.cz/~urban/MizarModeDoc/html"
"The HTML help for Mizar Mode resides here.")

(defun mizar-browse-as-html (&optional suffix)
"Browse in a HTML browser the article or an environment file.
A XSLT-capable browser like Mozilla or IE has to be default in
Emacs - you may need to customize the variable
`browse-url-browser-function' for this, and possibly (if 
the previous is set to `browse-url-generic') also the variable 
`browse-url-generic-program'.  Argument SUFFIX is a
file suffix to use."
(interactive)
(let* ((name (file-name-sans-extension (buffer-file-name)))
       (xmlname (concat name ".xml")))  
  (or (and
       (not (buffer-modified-p))
       (file-readable-p xmlname)
       (equal last-verification-date (file-mtime (buffer-file-name))))
      (error "Run verifier before browsing HTML!"))
  (if (not suffix)
      (browse-url (concat "file://" xmlname))
    (let* ((oldname (concat name "." suffix))
	   (newname (concat oldname ".xml")))
      (copy-file oldname newname t t)
      (browse-url (concat "file://" newname))))))

(defun mizar-browser-customize ()
"Set Mozilla (Firefox) as the default browser"
(interactive)
;; check that `browse-url-mozilla' exists
(if (functionp 'browse-url-mozilla)
    (customize-save-variable 'browse-url-browser-function 
			     'browse-url-mozilla)
  (customize-save-variable 'browse-url-browser-function 
			   'browse-url-generic)
  (customize-variable 'browse-url-generic-program)
  )
)

;;;;;;;;;;;;;;;   AR 4 mizar and html and mw services
(defcustom ar4mizar-server "http://mws.cs.ru.nl/"
"Server for the AR4Mizar services."
:type 'string
:group 'mizar-proof-advisor)


(defcustom ar4mizar-cgi "~mptp/cgi-bin/MizAR.cgi"
"Path to the ar4mizar CGI script on `ar4mizar-server'."
:type 'string
:group 'mizar-proof-advisor)

;; this sucks - the article is encoded as cgi argument of http-get
(defun mizar-post-to-ar4mizar-old (&optional suffix)
"Browse in a HTML browser the article or an environment file.
A XSLT-capable browser like Mozilla or IE has to be default in
Emacs - you may need to customize the variable
`browse-url-browser-function' for this, and possibly (if 
the previous is set to `browse-url-generic') also the variable 
`browse-url-generic-program'.  Argument SUFFIX is a
file suffix to use."
(interactive)
(let* ((aname (file-name-nondirectory
		(file-name-sans-extension
		 (buffer-file-name)))))
      (browse-url (concat ar4mizar-server ar4mizar-cgi "?Formula=" (query-handle-chars-cgi (buffer-string)) "&Name=" aname))))

;; borrowed from somewhere - http-post code
;; the problem is to pass things to a browser
(defun my-url-http-post (url args)
      "Send ARGS to URL as a POST request."
      (let ((url-request-method "POST")
            (url-request-extra-headers
             '(("Content-Type" . "application/x-www-form-urlencoded")))
            (url-request-data
             (mapconcat (lambda (arg)
                          (concat (url-hexify-string (car arg))
                                  "="
                                  (url-hexify-string (cdr arg))))
                        args
                        "&")))
        ;; if you want, replace `my-switch-to-url-buffer' with `my-kill-url-buffer'
        (url-retrieve url 'my-switch-to-url-buffer)))

    (defun my-kill-url-buffer (status)
      "Kill the buffer returned by `url-retrieve'."
      (kill-buffer (current-buffer)))

    (defun my-switch-to-url-buffer (status)
      "Switch to the buffer returned by `url-retreive'.
    The buffer contains the raw HTTP response sent by the server."
      (switch-to-buffer (current-buffer)))


;; this is good, but only for getting errors or other text info
;; it does not launch browser
(defun mizar-post-to-ar4mizar-new1 (&optional suffix)
"Browse in a HTML browser the article or an environment file.
A XSLT-capable browser like Mozilla or IE has to be default in
Emacs - you may need to customize the variable
`browse-url-browser-function' for this, and possibly (if 
the previous is set to `browse-url-generic') also the variable 
`browse-url-generic-program'.  Argument SUFFIX is a
file suffix to use."
(interactive)
(let* ((aname (file-name-nondirectory
		(file-name-sans-extension
		 (buffer-file-name)))))
(my-url-http-post (concat ar4mizar-server ar4mizar-cgi) `(("Formula" . ,(buffer-substring-no-properties (point-min) (point-max))) ("Name" . ,aname)))))

;; the current version - creates a local html file with form
;; that gts submitted on-load
;; TODO: use mml.ini as additional argument selecting the library version
(defun mizar-post-to-ar4mizar (&optional htmlonly)
"Send the contents of the buffers to the MizAR service.
With prefix argument, only htmlize, do not crete atp problems and links.
Browse result in a HTML browser.
A browser like Mozilla or IE has to be default in
Emacs - you may need to customize the variable
`browse-url-browser-function' for this, and possibly (if 
the previous is set to `browse-url-generic') also the variable 
`browse-url-generic-program'."
(interactive "*P")
(let* ((fname (buffer-file-name))
       (aname (file-name-nondirectory
		(file-name-sans-extension
		 fname)))
       (requestfile (concat fname ".html"))
       (contents (htmlize-protect-string (buffer-substring-no-properties (point-min) (point-max))))
       (htmlcontents (concat 
		      mizar-ar4mizar-html-start contents 
		      "</textarea><INPUT TYPE=\"hidden\" NAME=\"Name\" VALUE=\"" aname 
		      "\"> <INPUT TYPE=\"submit\" VALUE=\"Send\">"
		      (if htmlonly "" "<INPUT TYPE=\"hidden\" NAME=\"GenATP\" VALUE=\"1\">") 
		      "</FORM> </body> </html>" 
		      )))
  (with-temp-buffer
    (insert htmlcontents)
    (write-region (point-min) (point-max) requestfile))
(browse-url (concat "file:///" requestfile))))

;; stolen from htmlize.el
(defvar htmlize-basic-character-table
  ;; Map characters in the 0-127 range to either one-character strings
  ;; or to numeric entities.
  (let ((table (make-vector 128 ?\0)))
    ;; Map characters in the 32-126 range to themselves, others to
    ;; &#CODE entities;
    (dotimes (i 128)
      (setf (aref table i) (if (and (>= i 32) (<= i 126))
			       (char-to-string i)
			     (format "&#%d;" i))))
    ;; Set exceptions manually.
    (setf
     ;; Don't escape newline, carriage return, and TAB.
     (aref table ?\n) "\n"
     (aref table ?\r) "\r"
     (aref table ?\t) "\t"
     ;; Escape &, <, and >.
     (aref table ?&) "&amp;"
     (aref table ?<) "&lt;"
     (aref table ?>) "&gt;"
     ;; Not escaping '"' buys us a measurable speedup.  It's only
     ;; necessary to quote it for strings used in attribute values,
     ;; which htmlize doesn't do.
     ;(aref table ?\") "&quot;"
     )
    table))

(defun htmlize-protect-string (string)
  (mapconcat (lambda (char) (aref htmlize-basic-character-table char)) string ""))

(defvar  mizar-ar4mizar-html-start "
<html> <head> <title>Automated Reasoning for Mizar</title>
<script language=\"JavaScript\">
function myfunc () {
var frm = document.getElementById(\"myform\");
frm.submit();
}
window.onload = myfunc;
</script>
  </head> <body>
        <FORM ID=\"myform\" METHOD=\"POST\"  ACTION=\"http://mws.cs.ru.nl/~mptp/cgi-bin/MizAR.cgi\" enctype=\"multipart/form-data\">
            <INPUT TYPE=\"hidden\" NAME=\"ProblemSource\" VALUE=\"Formula\">
		<textarea name=\"Formula\" tabindex=\"3\"  rows=\"8\" cols=\"80\" id=\"FORMULAEProblemTextBox\">"
)


;; Menu for the mizar editing buffers
(defvar mizar-menu
  '(list  "Mizar"
	  ["Customize Mizar Mode" (customize-group 'mizar) t]
	  ["Browse HTML Help" (browse-url html-help-url) t]	  
	  '("Goto errors"
	    ["Next error"  mizar-next-error t]
	    ["Previous error" mizar-previous-error t]
	    ["Remove error lines" mizar-strip-errors t])
	  "-"
	  '("Browsing in abstracts"
	    ["View symbol def" mizar-symbol-def t]
	    ["Show reference" mizar-show-ref t]
	    ["Visited symbols" mouse-find-tag-history t]
	    ["Symbol apropos" symbol-apropos t]
	    ["Bury all abstracts" mizar-bury-all-abstracts t]
	    ["Close all abstracts" mizar-close-all-abstracts t]
	    )
	  '("Browse as HTML" 
	    :help "Mizar has to be run first. Mozilla or IE needed."
	    ["Browse current article" (mizar-browse-as-html) t]
	    ["Browse environmental clusters" (mizar-browse-as-html "ecl") t]
	    ["Browse environmental theorems" (mizar-browse-as-html "eth") t]
	    ["Browse environmental constructors" (mizar-browse-as-html "atr") t]
	    ["Browse environmental notations" (mizar-browse-as-html "eno") t]
	    ["Set Mozilla (Firefox) as the default browser" 
	     (mizar-browser-customize) t]
	    )
	  '("MoMM"
	    ["Use MoMM (needs to be installed)" mizar-toggle-momm :style toggle
	     :selected mizar-use-momm  :active t]
	    ["Load theorems only"  (setq mizar-momm-load-tptp
					 (not mizar-momm-load-tptp))
	     :style toggle :selected (not mizar-momm-load-tptp)
	     :active mizar-use-momm]
	    ["Run MoMM for current article"
	     (mizar-run-momm-default nil nil mizar-momm-load-tptp)
	     mizar-use-momm]
	    ["Load additional files in MoMM" mizar-momm-add-files
	     mizar-use-momm]
	    ["Run MoMM with parameters" mizar-run-momm mizar-use-momm]
	    ["Run MoMM with all.ths (200M!)" mizar-run-momm-full
	     mizar-use-momm]
	    ["MoMM export current article"
	     (progn
	       (mizar-it mizar-relcprem)
	       (mizar-it mizar-momm-exporter))
	     mizar-use-momm]
	    )
	  '("Mizar TWiki"
	    ["Browse Mizar Twiki" (browse-url mizar-twiki-url) t]
	    ["Ask Mizar question" (browse-url mizar-twiki-questions) t]
	    ["Suggest feature" (browse-url mizar-twiki-features) t]
	    ["Comment Mizar error" mizar-twiki-comment-error t]
	    ["Describe pitfall" (browse-url mizar-twiki-pitfalls) t]
	    ["View FAQ" (browse-url mizar-twiki-faq) t]
	    ["Report bug" (browse-url mizar-twiki-bugs) t]
	    ["MML Suggestions" (browse-url mizar-twiki-mml-sugg) t]
	    )
	  '("MML Query"	    
	    ["View MMLQuery abstract" mmlquery-find-abstract t
	     :help "Start Emacs MMLQuery browser for given abstract"]
	    ["Query window" query-start-entry t]
	    ("MML Query server"
	     ["Megrez" (setq query-url megrez-url) :style radio :selected (equal query-url megrez-url) :active t]
	     ["Merak" (setq query-url merak-url) :style radio :selected (equal query-url merak-url) :active t]
	     )
	    ("MML Query browser" 
	     :help "The preferred browser for WWW version of MMLQuery"
	     ["Emacs W3" (setq mizar-query-browser 'w3) :style radio :selected  (eq mizar-query-browser 'w3) :active t]
	     ["Default" (setq mizar-query-browser nil) :style radio :selected  (eq mizar-query-browser nil) :active t]
	     )
	    ["Show keybindings in *MML Query input*" (describe-variable 'query-entry-map) t]
	    )
	  '("Constr. Explanations"
	    :help "Explaining and browsing constructors in your formulas"
	    ("Verbosity" 
	     :help "Set to non-none to activate constructor explanations"
	    ["none" (mizar-toggle-cstr-expl 'none) :style radio :selected (not mizar-do-expl) :active t]
	    ["sorted constructors list" (mizar-toggle-cstr-expl 'sorted)
	     :style radio :selected
	     (and mizar-do-expl (eq mizar-expl-kind 'sorted)) :active t]
	    ["constructors list" (mizar-toggle-cstr-expl 'constructors)
	     :style radio :selected
	     (and mizar-do-expl (eq mizar-expl-kind 'constructors)) :active t]
	    ["mmlquery input" (mizar-toggle-cstr-expl 'mmlquery)
	     :style radio :selected
	     (and mizar-do-expl (eq mizar-expl-kind 'mmlquery)) :active t]
	    ["translated formula" (mizar-toggle-cstr-expl 'translate)
	     :style radio :selected
	     (and mizar-do-expl (eq mizar-expl-kind 'translate)) :active t]
;; 	    ["xml formula" (mizar-toggle-cstr-expl 'xml)
;; 	     :style radio :selected
;; 	     (and mizar-do-expl (eq mizar-expl-kind 'xml)) :active t]
;; 	    ["raw formula" (mizar-toggle-cstr-expl 'raw)
;; 	     :style radio :selected
;; 	     (and mizar-do-expl (eq mizar-expl-kind 'raw)) :active t]
	    )
	    ["Underline explanation points"
	     (setq mizar-underline-expls
		   (not mizar-underline-expls)) :style toggle :selected mizar-underline-expls  :active mizar-do-expl 
	      :help "Make the clickable explanation points underlined"]
	    ["Show keybindings in *Constructors list*" (describe-variable 'mizar-cstr-map) :active mizar-do-expl]
	    )
	  '("Grep"
	    ["Case sensitive" mizar-toggle-grep-case-sens :style
	     toggle :selected mizar-grep-case-sensitive :active t]
	    ["Grep in MML processing order" 
	     (customize-variable 'mizar-grep-in-mml-order)
	     :style toggle :selected mizar-grep-in-mml-order
	     :active t]
	    ["Abstracts" mizar-grep-abs t]
	    ["Full articles" mizar-grep-full :active t]
	    ["MML Query abstracts" mizar-grep-gab t]
	    ["Show positions for full-item grep" 
	     (customize-variable 'mizar-item-grep-show-lines)
	     :style toggle :selected mizar-item-grep-show-lines
	     :active t]
	    ["Full items in abstracts" mizar-grep-abs-full-items t]
	    ["Full items in MML Query abstracts" mizar-grep-gab-full-items 
	     :active t
	     :help "Also C-u C-c i"])	  
	  "-"
	  ["View theorems" mizar-make-theorem-summary t]
	  ["Reserv. before point" mizar-make-reserve-summary t]
	  "-"
	  ["Run Mizar" mizar-it (mizar-buf-verifiable-p)]
	  ["Accommodate & Run Mizar" (mizar-it nil nil nil nil t) (mizar-buf-verifiable-p)]
	  ["Mizar Compile" mizar-compile (mizar-buf-verifiable-p)]
	  ["Toggle quick-run" toggle-quick-run :style toggle :selected mizar-quick-run  :active (eq mizar-emacs 'gnuemacs)]
	  (list "Show output"
		["none" (mizar-toggle-show-output "none") :style radio :selected (equal mizar-show-output "none") :active t]
		["4 lines" (mizar-toggle-show-output 4) :style radio :selected (equal mizar-show-output 4) :active t]
		["10 lines" (mizar-toggle-show-output 10) :style radio :selected (equal mizar-show-output 10) :active t]
		["all" (mizar-toggle-show-output "all") :style radio :selected (equal mizar-show-output "all") :active t]
		)
	  (list "Show error"
		["none" (mizar-toggle-goto-error "none") :style radio :selected (equal mizar-goto-error "none") :active t]
		["first" (mizar-toggle-goto-error "first") :style radio :selected (equal mizar-goto-error "first") :active t]
		["next" (mizar-toggle-goto-error "next") :style radio :selected (equal mizar-goto-error "next") :active t]
		["previous" (mizar-toggle-goto-error "previous") :style radio :selected (equal mizar-goto-error "previous") :active t]
		)
	  "-"
	  (list "Voc. & Constr. Utilities"
		["Findvoc" mizar-findvoc t]
		["Listvoc" mizar-listvoc t]
		["Constr" mizar-constr t])
	  (list "Irrelevant Utilities"	    
	    ["Execute all irrelevant utils" mizar-run-all-irr-utils 
	     (mizar-buf-verifiable-p)]
	    ["Irrelevant Premises" mizar-relprem (mizar-buf-verifiable-p)]
	    ["Irrelevant Inferences" mizar-relinfer (mizar-buf-verifiable-p)]
	    ["Irrelevant Iterative Steps" mizar-reliters (mizar-buf-verifiable-p)]
	    ["Irrelevant Labels" mizar-chklab (mizar-buf-verifiable-p)]
	    ["Inaccessible Items" mizar-inacc (mizar-buf-verifiable-p)]
	    ["Trivial Proofs" mizar-trivdemo (mizar-buf-verifiable-p)]
	    (list "Environmental Utils"
		  ["Irrelevant Theorems" mizar-irrths (mizar-buf-verifiable-p)]
		  ["Irrelevant Vocabularies" mizar-irrvoc (mizar-buf-verifiable-p)]
		  )
	    )
	  '("Other Utilities"
	    ["Miz2Prel" (mizar-it "miz2prel" t) (eq mizar-emacs 'gnuemacs)]
	    ["Miz2Abs" (mizar-it "miz2abs" t) (eq mizar-emacs 'gnuemacs)]
	    ["Ratproof" (mizar-it "ratproof") t])
	  "-"
	  ["Insert proof skeleton" mizar-insert-skeleton 
	   :active (mizar-buf-verifiable-p)
	   :help "Formula being proved has to be selected"]
	  ["Comment region" comment-region t]
;; uncomment-region is not present in older Emacs
	  ["Uncomment region" (if (fboundp 'uncomment-region) 
				  (uncomment-region (region-beginning)
						    (region-end))
				(comment-region (region-beginning)
						(region-end) '(4))) 
	   :active t
	   :help "Also C-u C-c C-c"]
	  '("Proof checking"
	    ["proof -> @proof on region" mizar-hide-proofs t]
	    ["@proof -> proof on region" (mizar-hide-proofs (region-beginning)
							   (region-end) t) t]
	    ["proof -> @proof on buffer" (mizar-hide-proofs (point-min)
							   (point-max)) t]
	    ["@proof -> proof on buffer" (mizar-hide-proofs (point-min)
							   (point-max) t) t]
	    )
	  '("Then placement"
	    ["start of lines on region" mizar-move-then t]
	    ["end of lines on region" (mizar-move-then (region-beginning)
							  (region-end) t) t]
	    ["start of lines on buffer" (mizar-move-then (point-min)
							  (point-max)) t]
	    ["end of lines on buffer" (mizar-move-then (point-min)
							  (point-max) t) t]
	    )
	  "-"
	  '("Indenting"
	    ["Customize Indenting" (customize-group 'mizar-indenting) t]
	    ["Newline indents"  (setq mizar-newline-indents
				      (not mizar-newline-indents))
	     :style toggle :selected mizar-newline-indents :active t]
	     ["Semicolon indents"  (setq mizar-semicolon-indents
					 (not mizar-semicolon-indents))
	     :style toggle :selected mizar-semicolon-indents :active t]
	    ["Indent line" mizar-indent-line t]
	    ["Indent region" indent-region t]
	    ["Indent buffer" mizar-indent-buffer t]
	    '("Indent width"
	      ["1" (mizar-set-indent-width 1) :style radio :selected (= mizar-indent-width 1) :active t]
	      ["2" (mizar-set-indent-width 2) :style radio :selected (= mizar-indent-width 2) :active t]
	      ["3" (mizar-set-indent-width 3) :style radio :selected (= mizar-indent-width 3) :active t])
	    )
;	  '("Fontify"
;	    ["Buffer" font-lock-fontify-buffer t])
	  )
  "The definition for the menu in the editing buffers."
  )


(defun mizar-menu ()
  "Add the menu in the editing buffer."
  (let ((menu (delete nil (eval mizar-menu))))
    (cond
     ((eq mizar-emacs 'gnuemacs)
      (easy-menu-define mizar-menu-map mizar-mode-map "" menu))
     ((eq mizar-emacs 'xemacs)
      (easy-menu-add menu))
     ;; The default
     (t
      (easy-menu-define mizar-menu-map mizar-mode-map "" menu))
     )))

(mizar-menu)


(defun mizar-hs-forward-sexp (arg)
  "Function used by function `hs-minor-mode' for `forward-sexp' in Mizar mode.
Move forward across one balanced expression (sexp).
With ARG, do it that many times.  Negative arg -N means
move backward across N balanced expressions."
(let ((both-regexps (concat "\\(" hs-block-start-regexp "\\)\\|\\("
			      hs-block-end-regexp "\\)")
      ))
  (if (< arg 0)
      (backward-sexp 1)
    (if (looking-at hs-block-start-regexp)
	(let (beg1 end1 result1 prec)
	  (forward-sexp 1)
	  (setq count 1)
	  (while (and (> count 0) (not (eobp)))
	    (re-search-forward both-regexps (point-max) t nil)
	    (setq beg1  (match-beginning 0))
	    (setq end1 (match-end 0))
	    (setq result1 (buffer-substring-no-properties beg1 end1))
	    ;; check for preceding comment 
	    (forward-line 0)
	    (setq prec  (buffer-substring-no-properties (point) beg1))
	    (if (string-match "::" prec)
		(forward-line 1)
	      (goto-char end1)
	      (if (string-match hs-block-start-regexp result1)
		  (setq count (+  count 1))
		(setq count (- count 1)))))
	  (goto-char (match-end 0)))
	  ))))

(defun mizar-hs-adjust-block-beginning (pos)
  "Adjust the block that we are looking at."
  (save-excursion
    (goto-char pos)
    (forward-word -1)
    (point)))


(let ((mizar-mode-hs-info '(mizar-mode "\\b\\(proof\\|now\\|hereby\\|case\\|suppose\\)[ \n\r]" "end;" "::+" mizar-hs-forward-sexp mizar-hs-adjust-block-beginning)))
    (if (not (member mizar-mode-hs-info hs-special-modes-alist))
            (setq hs-special-modes-alist
	                  (cons mizar-mode-hs-info hs-special-modes-alist))))
;(add-hook 'mizar-mode-hook 'mizar-menu)
(defun mizar-set-pp-level (level)
  "Set the presentation level to LEVEL.  This is done by calling `hs-hide-level' on top level."
  (interactive "n")
  (save-excursion
    (goto-char (point-min))
    (hs-hide-level level)))

(setq mizar-abs-map (make-sparse-keymap))
(easy-menu-define mizar-abs-menu
  mizar-abs-map
  "Submenu of hide/show used for items in Mizar abstracts."
  '(""
    ["Theorems" mizar-abs-toggle-th :style radio 
     :selected (not (memq 'theorem buffer-invisibility-spec)) :active t
     :help "Toggle hiding of theorems" ]
    
    ["Definitions" mizar-abs-toggle-def :style radio 
     :selected (not (memq 'definition buffer-invisibility-spec)) :active t
     :help "Toggle hiding of definitions" ]
    ["Schemes" mizar-abs-toggle-sch :style radio 
     :selected (not (memq 'scheme buffer-invisibility-spec)) :active t
     :help "Toggle hiding of schemes" ]
    ["Registrations" mizar-abs-toggle-reg :style radio 
     :selected (not (memq 'registration buffer-invisibility-spec)) :active t
     :help "Toggle hiding of registrations" ]
    ["Notations" mizar-abs-toggle-not :style radio 
     :selected (not (memq 'notation buffer-invisibility-spec)) :active t
     :help "Toggle hiding of notations" ]
    ["Reservations" mizar-abs-toggle-res :style radio 
     :selected (not (memq 'reserve buffer-invisibility-spec)) :active t
     :help "Toggle hiding of reservations" ]
    ["Canceled" mizar-abs-toggle-can :style radio 
     :selected (not (memq 'canceled buffer-invisibility-spec)) :active t
     :help "Toggle hiding of canceled theorems" ]
    ))

(define-key-after hs-minor-mode-menu [mizar-hs-abstract-items]
  `(menu-item  "Hide/Show items in abstracts" 
	       ,mizar-abs-menu
	       :enable (buffer-abstract-p (current-buffer))))

(define-key-after hs-minor-mode-menu [pres-global]
  `(menu-item  "Global Proof Presentation Level" 
	       (keymap "Global Proof Presentation Level" 
		(0 menu-item "0" 
		   ,(lambda () (interactive) (mizar-set-pp-level 1)))
		(1 menu-item "1" 
		   ,(lambda () (interactive) (mizar-set-pp-level 2)))
		(2 menu-item "2" 
		   ,(lambda () (interactive) (mizar-set-pp-level 3)))
		(3 menu-item "3" 
		   ,(lambda () (interactive) (mizar-set-pp-level 4)))
		(4 menu-item "4" 
		   ,(lambda () (interactive) (mizar-set-pp-level 5)))
		(all menu-item "all" hs-show-all))))

(define-key-after hs-minor-mode-menu [pres-current]
  `(menu-item  "Current Proof Presentation Level" 
	       (keymap "Global Proof Presentation Level" 
		(0 menu-item "0" 
		   ,(lambda () (interactive) (hs-hide-level 1)))
		(1 menu-item "1" 
		   ,(lambda () (interactive) (hs-hide-level 2)))
		(2 menu-item "2" 
		   ,(lambda () (interactive) (hs-hide-level 3)))
		(3 menu-item "3" 
		   ,(lambda () (interactive) (hs-hide-level 4)))
		(4 menu-item "4" 
		   ,(lambda () (interactive) (hs-hide-level 5)))
		(all menu-item "all" 
		     ,(lambda () (interactive) (hs-hide-level 100))))))
(add-hook 'mizar-mode-hook 'hs-minor-mode)
(add-hook 'mizar-mode-hook 'imenu-add-menubar-index)
;; adding this as a hook causes an error when opening
;; other file via speedbar, so we do it the bad way
;;(if (featurep 'speedbar)
;;    (add-hook 'mizar-mode-hook '(lambda () (speedbar 1))))
(if (and window-system (featurep 'speedbar) mizar-launch-speedbar)
    (speedbar 1))

(provide 'mizar)

;;; mizar.el ends here
