;;; spl-mode.el -- Emacs mode for GRASShopper programs.

;; Copyright (c) 2013-2018 Thomas Wies <wies@cs.nyu.edu>>
;;
;; Author: Thomas Wies
;; URL: http://cs.nyu.edu/wies/software/grasshopper
;; Version: 0.5

;;; Commentary:

;; Major mode for editing GRASShopper programs.

;; Features:
;; - syntax highlighting
;; - automated indentation
;; - on-the-fly syntax and type checking
;; - compilation mode for verification

;; Keyboard shortcuts:
;; C-c C-v -- Verify current buffer
;; C-c C-p -- Verify enclosing procedure/lemma of position in current buffer

;;; Code:

(require 'font-lock)
(if (<= 20 emacs-major-version)
    (defun make-regexp (a b c) (regexp-opt a b))
  (require 'make-regexp))

(cond
 ((x-display-color-p)
  (make-face 'Spec)
  (set-face-foreground 'Spec "magenta4")
  (setq font-lock-spec-face 'Spec)
))


(defconst spl-defuns '("define" "function" "predicate" "lemma" "procedure" "struct" "type" "datatype" 
                         "pure function" "pure predicate" "include" "var"))

(defconst spl-specifiers '("axiom" "ensures" "free" "invariant" "requires" "pure" "assert" "assume" "split" "returns"))

(defconst spl-modifiers '("implicit" "ghost"))

(defconst spl-constants '("emp" "null" "true" "false"))

(defconst spl-builtins '("import"  "yields" "exists" "forall" "Btwn" "Reach" "Disjoint" "Frame" "in" "old" "subsetof"))

(defconst spl-keywords '("havoc" "free" "choose" "else" "if" "new" "return" "while" "matching" "yields" "without" "pattern" "known"))

;(defconst dafny-all-keywords (cl-loop for source in '(dafny-defuns dafny-specifiers dafny-modifiers
;                                                      dafny-builtins dafny-keywords dafny-types)
;                                      append (mapcar (lambda (kwd) (propertize kwd 'source source)) (symbol-value source))))

(defconst spl-defuns-regexp     (regexp-opt spl-defuns 'symbols))
(defconst spl-specifiers-regexp (regexp-opt spl-specifiers 'symbols))
(defconst spl-modifiers-regexp  (regexp-opt spl-modifiers 'symbols))
(defconst spl-constants-regexp  (regexp-opt spl-constants 'symbols))
(defconst spl-builtins-regexp   (regexp-opt spl-builtins 'symbols))
(defconst spl-keywords-regexp   (regexp-opt spl-keywords 'symbols))

(defconst spl-block-heads '("else" "if" "while"))
(defconst spl-extended-block-head-regexp (concat "\\s-*" (regexp-opt (append spl-block-heads spl-defuns) 'symbols)))
(defconst spl-extended-defun-regexp (concat "\\s-*" spl-defuns-regexp))


(defconst spl-mode-font-lock-keywords
  (list
   '("\\(//[^\n]*\\)" 1 
     font-lock-comment-face)

   (list spl-defuns-regexp
         '(1 font-lock-keyword-face))

   (list spl-specifiers-regexp
         '(1 font-lock-keyword-face))

   (list spl-modifiers-regexp
         '(1 font-lock-keyword-face))

   (list spl-keywords-regexp
         '(1 font-lock-keyword-face))

   (list spl-builtins-regexp
         '(1 font-lock-builtin-face))

   (list spl-constants-regexp
         '(1 font-lock-constant-face))
   
   '("\\(\\<[a-zA-Z_][a-zA-Z0-9_^']*\\>\\)[ \t]*(" 1
     font-lock-function-name-face)

   '("\\(\\<[A-Z_][a-zA-Z0-9_^']*\\>\\)" 1
     font-lock-type-face)

   '("\\<\\(forall\\|exists\\)[ \t]*\\([a-zA-Z_][a-zA-Z0-9_^']*\\)\\>" 2
     font-lock-variable-name-face)

   '("\\(\\<[a-zA-Z_][a-zA-Z0-9_^']*[ \t]*\\>\\):[^:=]" 1
     font-lock-variable-name-face)
   ))


(defvar spl-mode-syntax-table nil
  "Syntax table in use in spl-mode buffers.")

(if spl-mode-syntax-table
    ()
  (setq spl-mode-syntax-table (make-syntax-table))
  (modify-syntax-entry ?/ ". 14b" spl-mode-syntax-table)
  (modify-syntax-entry ?* ". 23b" spl-mode-syntax-table)
  (modify-syntax-entry ?\n ">" spl-mode-syntax-table)
  (modify-syntax-entry ?\f ">" spl-mode-syntax-table)
  (modify-syntax-entry ?' "w" spl-mode-syntax-table)
  (modify-syntax-entry ?_ "w" spl-mode-syntax-table)
  (modify-syntax-entry ?@ "w" spl-mode-syntax-table)
  (modify-syntax-entry ?$ "w" spl-mode-syntax-table)
)

(if (< 23 emacs-major-version)
    (define-derived-mode spl-mode c-mode "SPL"
      "Major mode for editing Grasshopper program files."
      :syntax-table spl-mode-syntax-table
      (setq-local comment-start "// ")
      (setq-local font-lock-defaults '(spl-mode-font-lock-keywords))
      (setq-local indent-line-function 'spl-indent-keep-position)
      )
  (setq font-lock-defaults-alist
        (cons (cons 'spl-mode 
                    '(spl-mode-font-lock-keywords
                      nil nil nil backward-paragraph
                      (font-lock-comment-start-regexp . "/[*/]")))
              font-lock-defaults-alist))
  (defun spl-mode ()
    "Major mode for editing Grasshopper program files"
    
    (interactive)

    (kill-all-local-variables)
    
    (setq mode-name "SPL")
    (setq major-mode 'spl-mode)
    (set-syntax-table spl-mode-syntax-table)
    (run-hooks 'spl-mode-hook)))

(defun spl-line-props ()
  "Classifies the current line (for indentation)."
  (save-excursion
    (beginning-of-line)
    (cons (cond ((or (comment-beginning) (looking-at-p "\\s-*/[/*]")) 'comment)
                ((looking-at-p "\\s-*\\(case\\|else\\)")              'case)
                ((looking-at-p ".*{\\s-*\\(//.*\\)?$")                'open)
                ((looking-at-p ".*}\\s-*\\(//.*\\)?$")                'close)
                ((looking-at-p ".*;\\s-*\\(//.*\\)?$")                'semicol)
                ((looking-at-p spl-extended-defun-regexp)             'defun)
                (t                                                    'none))
          (current-indentation))))

(defun spl-backward-line ()
  "Jump one line backwards, and then skip over blank lines."
  (forward-line 0)
  (/= 0 (skip-chars-backward "\r\n\t ")))

(defun spl-indent ()
  "Indent current line."
  (interactive)
  (beginning-of-line)
  (let* ((pprev-type  (car-safe (save-excursion (and (spl-backward-line) (spl-backward-line) (spl-line-props)))))
         (prev-props  (save-excursion (and (spl-backward-line) (spl-line-props))))
         (prev-type   (car-safe prev-props))
         (prev-offset (or (cdr-safe prev-props) 0))
         (is-defun    (looking-at-p spl-extended-defun-regexp))
         (is-close    (looking-at-p "[^{\n]*}"))
         (is-lonely-open (looking-at-p "[ \t]*{"))
         (is-else    (looking-at-p "[ \t]*else"))
         (comment-beg (save-excursion (comment-beginning))))
    (indent-line-to
     (cond (comment-beg (if (< comment-beg (point-at-bol)) ;; Multiline comment; indent to '*' or beginning of text
                            (let ((incr (if (looking-at-p "\\s-*\\*") 1 3)))
                              (save-excursion (goto-char comment-beg) (+ (current-indentation) incr)))
                          prev-offset))
           ((or is-close is-lonely-open)
            (save-excursion
              (when is-close
                (backward-up-list))
              ;; Find beginning of block head (the head can span multiple lines)
              (let ((bound (save-excursion (ignore-errors (backward-up-list) (point)))))
                ;; The bound ensures that brackets headerless blocks are indented properly
                (re-search-backward (concat "^\\s-*}?" spl-extended-block-head-regexp) bound t))
              (current-indentation)))
           (is-defun (if (memq prev-type '(open)) (+ prev-offset c-basic-offset) prev-offset))
           ;(is-case (-if-let (parent (save-excursion (when (re-search-backward "^\\s-*match" nil t) (current-indentation))))
           ;             (indent-next-tab-stop parent)
           ;           prev-offset))
           (is-else (or (save-excursion (when (re-search-backward "^\\s-*if" nil t) (current-indentation)))
                        prev-offset))
           (t (pcase prev-type
                (`comment prev-offset)
                (`case    (+ prev-offset c-basic-offset))
                (`open    (+ prev-offset c-basic-offset))
                (`close   prev-offset)
                (`semicol prev-offset)
                (`defun   (+ prev-offset c-basic-offset))
                (`none    (if (memq pprev-type '(none defun comment case)) prev-offset (+ prev-offset c-basic-offset)))
                (_        prev-offset))))))
  (skip-chars-forward " "))


(defun spl-indent-keep-position ()
  "Indent current line, minimally moving point.
That is, leaves the point in place if it is already beyond the
first non-blank character of that line, and moves it to the first
character in the line otherwise."
  (interactive)
  (let ((position (save-excursion (spl-indent) (point))))
    (when (> position (point))
      (goto-char position))))

(or (assoc "\\.spl$" auto-mode-alist)
    (setq auto-mode-alist (cons '("\\.spl$" . spl-mode)
				auto-mode-alist)))

(add-hook 'spl-mode-hook
          (lambda ()
            (push '("::" . ?∷) prettify-symbols-alist)
            (push '("==>" . ?⟹) prettify-symbols-alist)
            (push '("|->" . ?↦) prettify-symbols-alist)
            (push '("->" . ?⟶) prettify-symbols-alist)
            (push '("&*&" . ?✶) prettify-symbols-alist)
            (push '("&+&" . ?⊕) prettify-symbols-alist)
            (push '("&&" . ?∧) prettify-symbols-alist)
            (push '("||" . ?∨) prettify-symbols-alist)
            (push '("**" . ?∩) prettify-symbols-alist)
            (push '("++" . ?∪) prettify-symbols-alist)
            (push '("--" . ?—) prettify-symbols-alist)
            (push '("in" . ?∈) prettify-symbols-alist)
            (push '("!in" . ?∉) prettify-symbols-alist)
            (push '("subsetof" . ?⊆) prettify-symbols-alist)
            (push '("!=" . ?≠) prettify-symbols-alist)
            (push '("!" . ?¬) prettify-symbols-alist)
            (push '("forall" . ?∀) prettify-symbols-alist)
            (push '("exists" . ?∃) prettify-symbols-alist)
            (push '("<=" . ?≤) prettify-symbols-alist)
            (push '(">=" . ?≥) prettify-symbols-alist)
            (prettify-symbols-mode)))

;; Flycheck mode specific settings
(when (require 'flycheck nil :noerror)
  ;; Define syntax and type checker
  (flycheck-define-checker spl-reporter
    "Syntax and type checker for GRASShopper programs."
    :command ("grasshopper" "-basedir" (eval (flycheck-d-base-directory)) "-lint" "-typeonly" source)
    :error-patterns
    ((warning line-start (file-name) ":" line ":" column (optional "-" end-column) ":Related Location:" (message) line-end)
     (error line-start (file-name) ":" line ":" column (optional "-" end-column) ":" (message) line-end))
    ;((error line-start (file-name) ":" line ":" column ":" (message) line-end))
    :modes (spl-mode))

  ;; Register syntax checker
  (add-hook 'spl-mode-hook (lambda ()
                             (setq flycheck-highlighting-mode 'columns)
                             (flycheck-select-checker 'spl-reporter)
                             (flycheck-mode)))

  ;; Define checker for verifying current buffer
  (flycheck-define-checker spl-verifier
    "On-the-fly verifier for GRASShopper programs."
    :command ("grasshopper" "-basedir" (eval (flycheck-d-base-directory)) "-lint" source "-smtsolver" "z3+cvc4")
    :error-patterns
   ((info line-start (file-name) ":" line ":" column (optional "-" end-column) ":Trace Information:" (message) line-end)
     (warning line-start (file-name) ":" line ":" column (optional "-" end-column) ":Related Location:" (message) line-end)
     (error line-start (file-name) ":" line ":" column (optional "-" end-column) ":" (message) line-end))
    ;((error line-start (file-name) ":" line ":" column ":" (message) line-end))
   :modes (spl-mode))

  ;; Define checker for verifying current procedure
  (defvar spl-current-procedure nil)
  (flycheck-define-checker spl-proc-verifier
    "On-the-fly verifier for GRASShopper programs."
    :command ("grasshopper" "-basedir" (eval (flycheck-d-base-directory)) "-smtsolver" "z3+cvc4" 
              "-procedure" (eval spl-current-procedure)
              "-model" "/tmp/model.html"
              "-lint" source)
    :error-patterns
    ((info line-start (file-name) ":" line ":" column (optional "-" end-column) ":Trace Information:" (message) line-end)
     (warning line-start (file-name) ":" line ":" column (optional "-" end-column) ":Related Location:" (message) line-end)
     (error line-start (file-name) ":" line ":" column (optional "-" end-column) ":" (message) line-end))
    ;((warning line-start "File \"" (file-name) "\", line " line ", columns " column (optional "-" end-column) ":" line-end "Related Location: " (message) line-end)
     ;(error line-start "File \"" (file-name) "\", line " line ", columns " column (optional "-" end-column) ":" line-end (message) line-end))
    ;((error line-start (file-name) ":" line ":" column ":" (message) line-end))
    :modes (spl-mode))

  (defun spl-show-model ()
    "Show counterexample model of the most recent failed verification attempt."
    (interactive)
    (browse-url-of-file "/tmp/model.html"))
  
  ;; Register keyboard shortcuts for verifier
  (defun spl-verify-buffer ()
    "Verify current buffer using GRASShopper."
    (interactive)
    (flycheck-select-checker 'spl-verifier)
    (flycheck-compile)
    (flycheck-select-checker 'spl-reporter))
  
  (defun spl-verify-procedure ()
    "Verify current procedure using GRASShopper."
    (interactive)
    (save-excursion
      (forward-line 0)
      (while (and (< 1 (string-to-number (format-mode-line "%l"))) (not (looking-at-p "[ \t]*\\(procedure\\|lemma\\)")))
        (forward-line (- 1)))
      (if (looking-at "[ \t]*\\(procedure\\|lemma\\)[ \t]+\\([^\s-(]+\\)")
          (let* ((proc-name (match-string 2)))
            (progn (message "Verifying procedure %s..." proc-name)
                   (setq spl-current-procedure proc-name)
                   (flycheck-select-checker 'spl-proc-verifier)
                   (flycheck-compile)
                   (flycheck-select-checker 'spl-reporter)))
        (message "Could not find enclosing procedure of current position."))))
  (add-hook 'spl-mode-hook
            (lambda () 
              (local-set-key (kbd "C-c C-v") 'spl-verify-buffer)
              (local-set-key (kbd "C-c C-p") 'spl-verify-procedure)
              (local-set-key (kbd "C-c C-m") 'spl-show-model))))

(add-hook 'compilation-finish-functions
           (lambda (buf str)
             (if (null (string-match ".*exited abnormally.*" str))
                 (message "%s" (propertize "Verification succeeded." 'face '(:foreground "darkgreen")))
               (message "%s" (propertize "Verification failed." 'face '(:foreground "red"))))))

(add-hook 'compilation-start-hook
          (lambda (proc)
            (let ((win  (get-buffer-window (get-buffer "*compilation*") 'visible)))
              (when win (delete-window win)))))

(provide 'spl-mode)

;;; spl-mode.el ends here

