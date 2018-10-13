#lang at-exp slideshow

;; Slides for GRACE 2018
;;
;; Date: 2018-11-04 (sunday)
;; Time: 13:55 -- 14:15
;; Topic: ICFP + DLS talks ... mostly ICFP, switch to DLS

(require
  gf-icfp-2018/talk/src/gt-system gf-icfp-2018/talk/src/constant
  pict pict/convert pict/balloon pict/shadow
  ppict/2
  scribble-abbrevs/pict
  slideshow/code
  plot/no-gui plot/utils
  racket/draw
  racket/list
  (only-in racket/string string-split)
  images/icons/arrow images/icons/control images/icons/misc images/icons/symbol images/icons/style
  (only-in scribble/base url))
