;;; spl-mode.el -- Emacs SPL mode


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

   '("\\<\\(if\\|else\\|free\\|pr\\(ocedure\\|edicate\\)\\|return\\(s\\|\\)\\|struct\\|var\\|while\\)\\>"
         1 font-lock-keyword-face)

   '("\\<\\(ass\\(ert\\|ume\\)\\|ensures\\|invariant\\|requires\\)\\>"
         1 font-lock-spec-face)

   '("\\<\\(forall\\|havoc\\|new\\|exists\\|old\\)\\>"
         1 font-lock-builtin-face)

   '("\\<\\(emp\\|false\\|null\\|true\\)\\>"
         1 font-lock-constant-face)

   '("\\(\\<[a-zA-Z_][a-zA-Z0-9_']*[ \t]*\\>\\)(" 1
     font-lock-function-name-face)

   '(":[ \t]*\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)" 1
     font-lock-type-face)

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

(setq font-lock-defaults-alist
      (cons (cons 'spl-mode 
                  '(spl-mode-font-lock-keywords
                    nil nil nil backward-paragraph
                    (font-lock-comment-start-regexp . "/[*]")))
            font-lock-defaults-alist))

(defun spl-mode ()
  "Major mode for editing SPL files"

  (interactive)

  (kill-all-local-variables)

  (setq mode-name "SPL")
  (setq major-mode 'spl-mode)
  (set-syntax-table spl-mode-syntax-table)
  (run-hooks 'spl-mode-hook))


(or (assoc "\\.spl$" auto-mode-alist)
    (setq auto-mode-alist (cons '("\\.spl$" . spl-mode)
				auto-mode-alist)))

(provide 'spl-mode)
