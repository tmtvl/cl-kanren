(defsystem "cl-kanren"
  :version "0.0.1"
  :author "Tim Van den Langenbergh  <tmt_vdl@gmx.com>"
  :license "AGPL-3.0"
  :home-page ""
  :bug-tracker ""
  :source-control (:git "")
  :depends-on ()
  :serial t
  :components ((:module "lisp"
                :serial t
                :components
                        ((:file "cl-kanren"))))
  :description ""
  :long-description
  #.(read-file-string
     (subpathname *load-pathname* "README.org"))
  :in-order-to ((test-op (test-op "cl-kanren-test"))))
