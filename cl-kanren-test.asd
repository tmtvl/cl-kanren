(defsystem "cl-kanren-test"
  :version "0.0.1"
  :author "Tim Van den Langenbergh  <tmt_vdl@gmx.com>"
  :license "AGPL-3.0"
  :depends-on (:cl-kanren)
  :serial t
  :components ((:module "test"
                :serial t
                :components
                        ((:file "cl-kanren"))))
  :description "Test suite for the cl-kanren system."
  :long-description
  #.(read-file-string
     (subpathname *load-pathname* "README.org")))
