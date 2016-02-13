; highlighting redexes

; the same as predefined highlight but with different color
(defface highlight2
  '((((class color) (min-colors 88) (background light))
     :background "slateBlue1")
    (((class color) (min-colors 88) (background dark))
     :background "slateBlue1")
    (((class color) (min-colors 16) (background light))
     :background "slateBlue1")
    (((class color) (min-colors 16) (background dark))
     :background "slateBlue1")
    (((class color) (min-colors 8))
     :background "slateBlue1" :foreground "black")
    (t :inverse-video t))
  "Basic face for highlighting."
  :group 'basic-faces)

(defun stepper-redex-highlight (prop)
  "highlight redexes"
  (progn
    (goto-char (point-max))
    (while (re-search-backward "\\[@stepper.redex\\]" nil t 1)
      ; (<p0>(<p1>true<p2>)<p3>[@stepper.str ]<p4>)
      (let* ((p3 (point))
	     (p4 (match-end 0))
	     (p2 (- p3 1)))
	(backward-list 1)
	(let* ((p0 (point))
	       (p1 (1+ p0)))
	  (add-text-properties p0 p1 '(invisible t))
	  (add-text-properties p1 p2 prop)
	  (add-text-properties p2 p3 '(invisible t))
	  (add-text-properties p3 p4 '(invisible t))
	  )))))

(defun stepper-remove-quotation ()
  "remove quotation marks"
  (progn
    (goto-char (point-min))
    (while (re-search-forward "\"" nil t 1)
      (add-text-properties (match-beginning 0) (match-end 0) '(invisible t)))))

(defun stepper-highlight ()
  "highlight redexes and remove quotation marks"
  (interactive)
  (progn
    (stepper-redex-highlight '(face highlight))
    (stepper-remove-quotation)
    ))
