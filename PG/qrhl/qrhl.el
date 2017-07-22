;(require ’proof-easy-config)

(defun qrhl-find-and-forget (span)
  (proof-generic-count-undos span))
  
(proof-easy-config 'qrhl "qRHL"
		   proof-prog-name "java -jar /home/unruh/.IdeaIC2017.1/config/plugins/Scala/launcher/sbt-launch.jar run"
		   proof-terminal-string "."
		   proof-shell-annotated-prompt-regexp "^\\(\\.\\.\\.\\|qrhl\\)> "
		   proof-script-comment-start-regexp "^\\s-*#"
		   proof-script-comment-end "\n"
		   proof-shell-error-regexp "\\[ERROR\\]\\|Exception"
		   proof-undo-n-times-cmd "undo %s."
		   proof-find-and-forget-fn 'qrhl-find-and-forget
		   proof-shell-start-goals-regexp "^[0-9]+ subgoals:\\|No current goal\\."
		   proof-shell-proof-completed-regexp "^No current goal.$"
		   )

(provide 'qrhl)


