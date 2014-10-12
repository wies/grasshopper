;;; package --- Summary
;;; spl-mode.el -- Emacs SPL mode

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

   '("\\<\\(i\\(f\\|nclude\\)\\|else\\|free\\|new\\|pr\\(ocedure\\|edicate\\)\\|return\\(s\\|\\)\\|struct\\|var\\|while\\)\\>"
         1 font-lock-keyword-face)

   '("\\<\\(ass\\(ert\\|ume\\)\\|ensures\\|havoc\\|i\\(mplicit\\|nvariant\\)\\|requires\\|ghost\\)\\>"
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
      ;(setq-local indent-line-function nil) 'c-indent-line)
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


(or (assoc "\\.spl$" auto-mode-alist)
    (setq auto-mode-alist (cons '("\\.spl$" . spl-mode)
				auto-mode-alist)))

(require 'compile)
(defun spl-errors ()
  (make-local-variable 'compilation-error-regexp-alist)
  (setq compilation-error-regexp-alist
        '("^File \"\\([_[:alnum:]-/]*.spl\\)\", line \\([[:digit:]]+\\), columns \\([[:digit:]]+\\)-.*\n\\(.*\\)$"
          1 2 3 4))
  (make-local-variable 'compile-command)
  (let ((grasshopper "grasshopper "))
    (setq compile-command (concat grasshopper buffer-file-name))))

(require 'flymake)
(defun flymake-spl-init ()
  (flymake-simple-make-init-impl
   'flymake-create-temp-with-folder-structure nil nil
   buffer-file-name
   'flymake-get-spl-cmdline))

(defun flymake-get-spl-cmdline (source base-dir)
    (list "grasshopper" (list "-lint" source)))

(add-hook 'spl-mode-hook
          '(lambda ()
             (add-to-list 'flymake-allowed-file-name-masks '(".+\\.spl$" flymake-spl-init))))

(add-hook 'spl-mode-hook
          '(lambda ()
             (add-to-list 'flymake-err-line-patterns
             '("^\\(.+\\):\\([[:digit:]]+\\):\\([[:digit:]]+\\)-\\([[:digit:]]+\\):\\(.*\\)$"
               1 2 3 5))))

(add-hook 'spl-mode-hook 'spl-errors)
(add-hook 'spl-mode-hook
          (lambda () (local-set-key (kbd "C-c C-c") 'compile)))

(when (require 'flycheck nil :noerror)
  (flycheck-define-checker spl-reporter
    "An SPL checker based on Grasshopper."
    :command ("grasshopper" "-lint" source)
    :error-patterns
    ((warning line-start (file-name) ":" line ":" column (optional "-" end-column) ":Related Location:" (message) line-end)
     (error line-start (file-name) ":" line ":" column (optional "-" end-column) ":" (message) line-end))
    ;((error line-start (file-name) ":" line ":" column ":" (message) line-end))
    :modes (spl-mode))
  (add-hook 'spl-mode-hook (lambda ()
                             (setq flycheck-highlighting-mode 'columns)
                             (flycheck-select-checker 'spl-reporter)
                             (flycheck-mode))))

(provide 'spl-mode)

;;; spl-mode.el ends here

