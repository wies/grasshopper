;;; package --- Summary
;;; spl-mode.el -- Emacs mode for GRASShopper programs.

;;; Commentary:

;;; Code:

(require 'font-lock)
(if (<= 20 emacs-major-version)
    (defun make-regexp (a b c) (regexp-opt a b))
  (require 'make-regexp))

(cond
 ((x-display-color-p)
  (make-face 'Firebrick)
  (set-face-foreground 'Firebrick "Firebrick")
  (make-face 'RosyBrown)
  (set-face-foreground 'RosyBrown "RosyBrown")
  (make-face 'Purple)
  (set-face-foreground 'Purple "Purple")
  (make-face 'MidnightBlue)
  (set-face-foreground 'MidnightBlue "MidnightBlue")
  (make-face 'DarkGoldenRod)
  (set-face-foreground 'DarkGoldenRod "DarkGoldenRod")
  (make-face 'Spec)
  (set-face-foreground 'Spec "magenta4")
  (make-face 'DarkOliveGreen)
  (set-face-foreground 'DarkOliveGreen "DarkOliveGreen4")
  (make-face 'CadetBlue)
  (set-face-foreground 'CadetBlue "CadetBlue")
  (make-face 'Stop)
  (set-face-foreground 'Stop "White")
  (set-face-background 'Stop "Red")
  (setq font-lock-reference-face 'CadetBlue)
  (setq font-lock-spec-face 'Spec)
  (setq font-lock-stop-face 'Stop)
  (setq font-lock-doc-face 'CadetBlue)
))


(defconst spl-mode-font-lock-keywords
  (list
   '("\\(//[^\n]*\\)" 1 
     font-lock-comment-face)

   '("\\<\\(i\\(f\\|nclude\\)\\|comment\\|else\\|f\\(ree\\|unction\\)\\|havoc\\|matching\\|new\\|outputs\\|pr\\(ocedure\\|edicate\\)\\|return\\(s\\|\\)\\|struct\\|var\\|while\\|yields\\)\\>"
         1 font-lock-keyword-face)

   '("\\<\\(ass\\(ert\\|ume\\)\\|ensures\\|i\\(mplicit\\|nvariant\\)\\|requires\\|ghost\\)\\>"
         1 font-lock-spec-face)

   '("\\<\\(old\\)\\>"
         1 font-lock-builtin-face)

   '("\\<\\(forall\\|exists\\|emp\\|false\\|in\\|null\\|true\\)\\>"
         1 font-lock-constant-face)

   '("\\(\\<[a-zA-Z_][a-zA-Z0-9_']*[ \t]*\\>\\)(" 1
     font-lock-function-name-face)

   '("[^:]:[ \t]*\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)" 1
     font-lock-type-face)

   '("<[ \t]*\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)[ \t]*>" 1
     font-lock-type-face)

   '("new[ \t]+\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)" 1
     font-lock-type-face)

   '("struct[ \t]+\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)" 1
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
                      (font-lock-comment-start-regexp . "/[*]")))
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
      (if (looking-at "[ \t]*invariant")
          0
        c-basic-offset)))
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
  (c-set-offset 'statement-cont 'spl-lineup-statement-cont)
  (c-set-offset 'statement 'spl-lineup-statement)
  (c-set-offset 'topmost-intro 'spl-lineup-topmost-intro)
  (c-set-offset 'defun-open 'spl-lineup-defun-open)
  (c-set-offset 'substatement-open 'spl-lineup-defun-open)
  (c-set-offset 'block-open 'spl-lineup-defun-open)
  ;;(c-set-offset 'substatement-open 0)
  (c-set-offset 'knr-argdecl-intro '+)
  (c-set-offset 'knr-argdecl 'spl-lineup-topmost-intro)
  (c-set-offset 'label '+))

(add-hook 'spl-mode-hook 'spl-set-indent)

(or (assoc "\\.spl$" auto-mode-alist)
    (setq auto-mode-alist (cons '("\\.spl$" . spl-mode)
				auto-mode-alist)))

;; Flycheck mode specific settings
(when (require 'flycheck nil :noerror)
  ;; Define syntax and type checker
  (flycheck-define-checker spl-reporter
    "Syntax and Type checker for Grasshopper programs."
    :command ("grasshopper" "-basedir" (eval (flycheck-d-base-directory)) "-lint" "-noverify" source)
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
    "On-the-fly verifier for Grasshopper programs."
    :command ("grasshopper" "-basedir" (eval (flycheck-d-base-directory)) "-lint" source)
    :error-patterns
    ((warning line-start (file-name) ":" line ":" column (optional "-" end-column) ":Related Location:" (message) line-end)
     (error line-start (file-name) ":" line ":" column (optional "-" end-column) ":" (message) line-end))
    ;((error line-start (file-name) ":" line ":" column ":" (message) line-end))
    :modes (spl-mode))

  ;; Register keyboard shortcut for verifier
  (defun spl-verify ()
    "Verify current buffer using GRASShopper."
    (interactive)
    (flycheck-select-checker 'spl-verifier)
    (flycheck-compile)
    (flycheck-select-checker 'spl-reporter))
  (add-hook 'spl-mode-hook
            (lambda () 
              (local-set-key (kbd "C-c C-v") 'spl-verify))))

(provide 'spl-mode)

;;; spl-mode.el ends here

