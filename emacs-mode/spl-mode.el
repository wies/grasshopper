;;; spl-mode.el -- Emacs mode for GRASShopper programs.

;; Copyright (c) 2013-2016 Thomas Wies <wies@cs.nyu.edu>>
;;
;; Author: Thomas Wies
;; URL: http://cs.nyu.edu/wies/software/grasshopper
;; Version: 0.4

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


(defconst spl-mode-font-lock-keywords
  (list
   '("\\(//[^\n]*\\)" 1 
     font-lock-comment-face)

   '("\\<\\(i\\(f\\|nclude\\)\\|c\\(hoose\\|omment\\)\\|define\\|else\\|f\\(ree\\|unction\\)\\|havoc\\|lemma\\|matching\\|new\\|or\\|p\\(attern\\|r\\(ocedure\\|edicate\\)\\)\\|return\\(s\\|\\)\\|struct\\|\\(data\\)?type\\|var\\|w\\(ithout\\|hile\\)\\|yields\\)\\>"
         1 font-lock-keyword-face)

   '("\\<\\(a\\(xiom\\|ss\\(ert\\|ume\\)\\)\\|ensures\\|i\\(mplicit\\|nvariant\\)\\|pure\\|requires\\|ghost\\|footprint\\|split\\)\\>"
         1 font-lock-keyword-face)

   '("\\<\\(Btwn\\|Disjoint\\|exists\\|forall\\|Frame\\|in\\|old\\|Reach\\|subsetof\\|&\\|!\\||\\|*\\|-\\|=\\|:\\|+\\)\\>"
         1 font-lock-builtin-face)

   '("\\<\\(emp\\|false\\|null\\|true\\)\\>"
         1 font-lock-constant-face)

   '("\\(\\<[a-zA-Z_][a-zA-Z0-9_']*[ \t]*\\>\\)(" 1
     font-lock-function-name-face)

   '("[^:]:[ \t]*\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)" 1
     font-lock-type-face)

   '("<[ \t]*\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)[ \t]*>" 1
     font-lock-type-face)

   '("<[ \t]*\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)[ \t]*<" 1
     font-lock-type-face)

   '("new[ \t]+\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)" 1
     font-lock-type-face)

   '("\\(struct\\|type\\)[ \t]+\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)" 2
     font-lock-type-face)

   '("\\<\\(forall\\|exists\\)[ \t]*\\([a-zA-Z_][a-zA-Z0-9_']*\\)\\>" 2
     font-lock-variable-name-face)

   '("\\(\\<[a-zA-Z_][a-zA-Z0-9_']*[ \t]*\\>\\):[^:=]" 1
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
      (setq-local indent-line-function 'c-indent-line)
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

(defun spl-set-indent ()
  (interactive)
  (defun spl-lineup-statement-cont (langelem)
    ;; lineup loop invariants
    (save-excursion
      (beginning-of-line)
      (if (looking-at "[ \t]*\\(invariant\\|while\\|//\\)")
          0
        (if (progn (goto-char (cdr langelem))
                   (looking-at "[ \t]*\\(function\\|predicate\\|{\\)"))
            0
          (if (and (not (looking-at "[ \t]*\\(invariant\\|assert\\|assume\\|pure\\|free\\|ensures\\|requires\\)"))
                   (looking-at ".*\\(&&\\|||\\)[ \t]*$"))
              0
            c-basic-offset)))))
  (defun spl-lineup-statement (langelem)
    ;; lineup loop invariants
    (save-excursion
      (beginning-of-line)
      (if (and (looking-at "[ \t]*invariant")
               (progn (goto-char (cdr langelem))
                      (not (looking-at "[ \t]*invariant"))))
          c-basic-offset
        0)))
  (defun spl-lineup-topmost-intro (langelem)
    ;; lineup procedure contracts
    (save-excursion
      (beginning-of-line)
      (if (looking-at "[ \t]*\\(requires\\|ensures\\)")
          (- c-basic-offset (c-langelem-col c-syntactic-element))
        0)))
  (defun spl-lineup-defun-open (langelem)
    ;; lineup block start after specs
    (save-excursion
      (goto-char (cdr langelem))
      (beginning-of-line)
      (if (looking-at "[ \t]*\\(invariant\\|ensures\\|requires\\)")
          (- 0 c-basic-offset)
        0)))
  (defun spl-lineup-block-open (langelem)
    ;; lineup block start after specs
    (save-excursion
      (goto-char (c-langelem-pos c-syntactic-element))
      (beginning-of-line)
      (if (looking-at "[ \t]*\\(invariant\\|ensures\\|requires\\)")
          (- 0 c-basic-offset)
        0)))
  (defun spl-lineup-topmost (langelem)
    (save-excursion
      (beginning-of-line)
      (if (looking-at "[ \t]*\\(axiom\\|lemma\\|procedure\\|function\\|predicate\\|struct\\|\\(data\\)?type\\)")
          0
        c-basic-offset)))
  (c-set-offset 'statement-cont 'spl-lineup-statement-cont)
  (c-set-offset 'statement 'spl-lineup-statement)
  (c-set-offset 'topmost-intro 'spl-lineup-topmost-intro)
  (c-set-offset 'defun-open 'spl-lineup-defun-open)
  (c-set-offset 'substatement-open 'spl-lineup-defun-open)
  (c-set-offset 'block-open 'spl-lineup-block-open)
  ;;(c-set-offset 'substatement-open 0)
  (c-set-offset 'knr-argdecl-intro 'spl-lineup-topmost)
  (c-set-offset 'topmost-intro-cont 'spl-lineup-topmost)
  (c-set-offset 'func-decl-cont 'spl-lineup-topmost)
  (c-set-offset 'knr-argdecl 'spl-lineup-topmost-intro)
  (c-set-offset 'label '+))

(add-hook 'spl-mode-hook 'spl-set-indent)

(or (assoc "\\.spl$" auto-mode-alist)
    (setq auto-mode-alist (cons '("\\.spl$" . spl-mode)
				auto-mode-alist)))

(add-hook 'spl-mode-hook
          (lambda ()
            (push '("::" . ?∷) prettify-symbols-alist)
            (push '("==>" . ?⟹) prettify-symbols-alist)
            (push '("|->" . ?↦) prettify-symbols-alist)
            (push '("->" . ?⟶) prettify-symbols-alist)
            ;(push '("(&*&)" . ?✹) prettify-symbols-alist)
            (push '("&*&" . ?✶) prettify-symbols-alist)
            (push '("&+&" . ?⊕) prettify-symbols-alist)
            (push '("&&" . ?∧) prettify-symbols-alist)
            (push '("||" . ?∨) prettify-symbols-alist)
            (push '("**" . ?∩) prettify-symbols-alist)
            ;(push '("(+*)" . ?⨄) prettify-symbols-alist)
            ;(push '("(++)" . ?⋃) prettify-symbols-alist)
            (push '("++" . ?∪) prettify-symbols-alist)
            (push '("--" . ?—) prettify-symbols-alist)
            (push '("in" . ?∈) prettify-symbols-alist)
            (push '("!in" . ?∉) prettify-symbols-alist)
            (push '("subsetof" . ?⊆) prettify-symbols-alist)
            (push '("!=" . ?≠) prettify-symbols-alist)
            ;(push '("==" . ?=) prettify-symbols-alist)
            (push '("!" . ?¬) prettify-symbols-alist)
            (push '("forall" . ?∀) prettify-symbols-alist)
            (push '("exists" . ?∃) prettify-symbols-alist)
            (push '("<=" . ?≤) prettify-symbols-alist)
            (push '(">=" . ?≥) prettify-symbols-alist)
            (prettify-symbols-mode)))

;; Flycheck mode specific settings
(when nil ;;(require 'flycheck nil :noerror)
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

