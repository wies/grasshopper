;;; ghp-mode.el -- Emacs GHP mode


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

(defconst ghp-mode-font-lock-keywords
  (list
   '("\\(//[^\n]*\\)" 1 
     font-lock-comment-face)

   '("\\<\\(check\\|forall\\|free ensures\\|free requires\\|e\\(xists\\|nsures\\)\\|ghost\\|invariant\\|old\\|requires\\)\\>"
         1 font-lock-spec-face)

   '("\\<\\(ass\\(ert\\|ume\\)\\|c\\(all\\|hoose\\)\\|free\\|havoc\\|locals\\|new\\|pr\\(ocedure\\|edicate\\)\\|or\\|return\\(s\\|\\)\\|var\\|while\\)\\>"
         1 font-lock-keyword-face)

   '("\\<\\(\\)\\>"
         1 font-lock-builtin-face)

   '("\\<\\(Frame\\|Btwn\\|false\\|in\\|null\\|true\\|Univ\\)\\>"
         1 font-lock-constant-face)

   '("\\(\\<[a-zA-Z_][a-zA-Z0-9_']*[ \t]*\\>\\)(" 1
     font-lock-function-name-face)

   '("[^:]:[ \t]*\\(\\<[a-zA-Z_][a-zA-Z0-9_']*\\>\\)" 1
     font-lock-type-face)

   '("\\(\\<[a-zA-Z_][a-zA-Z0-9_']*[ \t]*\\>\\):[^:=]" 1
     font-lock-variable-name-face)
   ))


(defvar ghp-mode-syntax-table nil
  "Syntax table in use in ghp-mode buffers.")

(if ghp-mode-syntax-table
    ()
  (setq ghp-mode-syntax-table (make-syntax-table))
  (modify-syntax-entry ?/ ". 14b" ghp-mode-syntax-table)
  (modify-syntax-entry ?* ". 23b" ghp-mode-syntax-table)
  (modify-syntax-entry ?\n ">" ghp-mode-syntax-table)
  (modify-syntax-entry ?\f ">" ghp-mode-syntax-table)
  (modify-syntax-entry ?' "w" ghp-mode-syntax-table)
  (modify-syntax-entry ?_ "w" ghp-mode-syntax-table)
  (modify-syntax-entry ?@ "w" ghp-mode-syntax-table)
  (modify-syntax-entry ?$ "w" ghp-mode-syntax-table)
)

(setq font-lock-defaults-alist
      (cons (cons 'ghp-mode 
                  '(ghp-mode-font-lock-keywords
                    nil nil nil backward-paragraph
                    (font-lock-comment-start-regexp . "/[*]")))
            font-lock-defaults-alist))

(defun ghp-mode ()
  "Major mode for editing Grasshopper program files"

  (interactive)

  (kill-all-local-variables)

  (setq mode-name "GHP")
  (setq major-mode 'ghp-mode)
  (set-syntax-table ghp-mode-syntax-table)
  (run-hooks 'ghp-mode-hook))


(or (assoc "\\.ghp$" auto-mode-alist)
    (setq auto-mode-alist (cons '("\\.ghp$" . ghp-mode)
				auto-mode-alist)))

(provide 'ghp-mode)
