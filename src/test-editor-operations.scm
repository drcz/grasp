;; -*- mode: scheme; *preserve-trailing-whitespace*: t -*-

(import
 (language define-syntax-rule)
 (language define-interface)
 (language define-type)
 (language define-object)
 (utils conversions)
 (editor interfaces elements)
 (editor types spaces)
 (editor document cursor)
 (editor types primitive)
 (editor text-painter)
 
 (editor types extensions extensions)
 (editor types extensions combinators)
 (editor document parse)
 (language examples)
 (language assert)
 (language infix)
 (language match)
 (language while)
 (utils functions)
 (utils print)
 (utils hash-table)
 (editor interfaces painting)
 (language for)
 (editor document document-operations)
 (editor document editor-operations)
 (editor document history-tracking)
 (editor interfaces painting)
 (editor text-painter)
 (editor document documents)
 )

(define verbose ::boolean #false)

(define (snapshot)::String
  (with ((painter (TextPainter)))
    (reset! extent-cached?)
    (draw-document! (the-document))
    (let ((result ::String (painter:toString)))
      (when verbose
	(display result))
      ;;(display (history (the-document)))
      result)))

(set! (the-document)
      (call-with-input-string
       "" parse-document))

(set! (the-cursor) (cursor 0 0 1))
(set! (the-selection-anchor) (the-cursor))

#|
(for-each insert-character! "\
[define [map f l]
  [march l
   [`[,h . ,t] `[,(f h) . ,[map f l]]]
   ['[]        '[]]")

(snapshot)

(exit)
|#

(insert-character! #\[)

(e.g.
 (snapshot) ===> "
╭  ╮
│  │
╰ |╯
")

(undo!)

(e.g.
 (snapshot) ===> "
")

(redo!)

(e.g.
 (snapshot) ===> "
╭  ╮
│  │
╰ |╯
")

(delete-backward!)

(e.g.
 (snapshot) ===> "
")

(undo!)

(e.g.
 (snapshot) ===> "
╭  ╮
│  │
╰ |╯
")

(for-each insert-character! '(#\d #\e #\f #\n #\e))

(e.g.
 (snapshot) ===> "
╭       ╮
│ defne │
╰      ^╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭  ╮
│  │
╰ |╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭       ╮
│ defne │
╰      ^╯
")

(times 2 delete-backward!)

(e.g.
 (snapshot) ===> "
╭     ╮
│ def │
╰    ^╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭       ╮
│ defne │
╰      ^╯
")

(times 2 move-cursor-left!)

(e.g.
 (snapshot) ===> "
╭       ╮
│ defne │
╰    ^  ╯
")

(insert-character! #\i)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
╰     ^  ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭       ╮
│ defne │
╰    ^  ╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
╰     ^  ╯
")

(times 2 move-cursor-right!)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
╰       ^╯
")

(insert-character! #\space)

(e.g.
 (snapshot) ===> "
╭         ╮
│ define  │
╰        |╯
")

(undo!)

;; Note: it is OK if the cursor isn't reverted faithfully,
;; as long as this does not affect re-playing history.

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
╰       |╯
")

(for-each insert-character! '(#\- #\c #\a #\c #\h #\e))

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰             ^╯
")
 
(undo!)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
╰       ^╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰             ^╯
")

(times 6 move-cursor-left!)

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰       ^      ╯
")


(insert-character! #\space)

(e.g.
 (snapshot) ===> "
╭               ╮
│ define -cache │
╰        |      ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰       ^      ╯
")

(insert-character! #\newline)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
│        │
│        │
│ -cache │
╰ |      ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰       ^      ╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
│        │
│        │
│ -cache │
╰ |      ╯
")

(delete-backward!)

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰       ^      ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
│        │
│        │
│ -cache │
╰ |      ╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰       ^      ╯
")

(times 6 move-cursor-right!)

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰             ^╯
")

(times 6 delete-backward!)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
╰       ^╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭              ╮
│ define-cache │
╰             ^╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭        ╮
│ define │
╰       ^╯
")

(insert-character! #\[)

(e.g.
 (snapshot) ===> "
╭       ╭  ╮ ╮
│ define│  │ │
╰       ╰ |╯ ╯
")

(times 2 move-cursor-left!)
(insert-character! #\space)
(times 2 move-cursor-right!)

(e.g.
 (snapshot) ===> "
╭        ╭  ╮ ╮
│ define │  │ │
╰        ╰ |╯ ╯
")

(for-each insert-character! '(#\! #\space #\n))

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
╰        ╰    ^╯ ╯
")

(times 3 move-cursor-right!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
╰        ╰     ╯|╯
")

(for-each insert-character! "
\"Computes the product")

(e.g.
 (snapshot) ===> "
╭        ╭     ╮           ╮
│ define │ ! n │           │
│        ╰     ╯           │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈• │
│ ┊ Computes the product ┊ │
╰ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞ ╯
")

(times 5 undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
│        ╰     ╯ │
│ ❝┈┈•           │
│ ┊  ┊           │
╰ •┈┈❞           ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
│        ╰     ╯ │
╰                ╯
                  
  |               
")

(times 3 redo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
│        ╰     ╯ │
│ ❝┈┈┈┈┈┈┈┈┈┈┈•  │
│ ┊ Computes  ┊  │
╰ •┈┈┈┈┈┈┈┈┈┈┈❞  ╯
")

(times 2 redo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮    ╮
│ define │ ! n │    │
│        ╰     ╯    │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈• │
│ ┊ Computes the  ┊ │
╰ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞ ╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮           ╮
│ define │ ! n │           │
│        ╰     ╯           │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈• │
│ ┊ Computes the product ┊ │
╰ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞ ╯
")

(times 20 delete-backward!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
│        ╰     ╯ │
│ ❝┈┈•           │
│ ┊  ┊           │
╰ •┈┈❞           ╯
")

(delete-backward!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
│        ╰     ╯ │
╰                ╯
                  
  |               
")

(undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
│        ╰     ╯ │
│ ❝┈┈•           │
│ ┊  ┊           │
╰ •┈┈❞           ╯
")

(times 2 undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ╮
│ define │ ! n │ │
│        ╰     ╯ │
│ ❝┈┈┈┈┈┈┈┈┈┈┈•  │
│ ┊ Computes  ┊  │
╰ •┈┈┈┈┈┈┈┈┈┈┈❞  ╯
")

(times 2 undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮    ╮
│ define │ ! n │    │
│        ╰     ╯    │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈• │
│ ┊ Computes the  ┊ │
╰ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞ ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮           ╮
│ define │ ! n │           │
│        ╰     ╯           │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈• │
│ ┊ Computes the product ┊ │
╰ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞ ╯
")

(for-each insert-character! "
1 * ... * n")

(e.g.
 (snapshot) ===> "
╭        ╭     ╮           ╮
│ define │ ! n │           │
│        ╰     ╯           │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈• │
│ ┊ Computes the product ┊ │
│ ┊ 1 * ... * n          ┊ │
╰ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞ ╯
")


(times 2 move-cursor-right!)

(for-each insert-character! "
[if [is n <= 1]
  1
 [* n [! [- n 1")

(e.g.
 (snapshot) ===> "
╭        ╭     ╮               ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰      ^╯ ╯ ╯ ╯ ╯
")

(set! (the-cursor) (cursor 0 4 1 1))
(set! (the-selection-anchor) (the-cursor))

(e.g.
 (snapshot) ===> "
╭        ╭     ╮               ╮
│ define │ ! n │               │
│        ╰     ╯|              │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(insert-character! #\space)
(insert-character! #\;)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾             ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮               ╮
│ define │ ! n │               │
│        ╰     ╯|              │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾             ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(for-each insert-character! " -> int")

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(set! (the-cursor) (cursor #\[ 7 1 1))
(set! (the-selection-anchor) (the-cursor))

(insert-character! #\;)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ ┊ i̶f̶ ┊ i̶s̶ n̶ <̶=̶ 1̶ ┊         ┊ │
│ ┊    ╰           ╯         ┊ │
│ ┊                          ┊ │
│ ┊   1̶                      ┊ │
│ ┊                          ┊ │
│ ┊  ╭     ╭   ╭       ╮ ╮ ╮ ┊ │
│ ┊  ┊ *̶ n̶ ┊ !̶ ┊ -̶ n̶ 1̶ ┊ ┊ ┊ ┊ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ ┊ i̶f̶ ┊ i̶s̶ n̶ <̶=̶ 1̶ ┊         ┊ │
│ ┊    ╰           ╯         ┊ │
│ ┊                          ┊ │
│ ┊   1̶                      ┊ │
│ ┊                          ┊ │
│ ┊  ╭     ╭   ╭       ╮ ╮ ╮ ┊ │
│ ┊  ┊ *̶ n̶ ┊ !̶ ┊ -̶ n̶ 1̶ ┊ ┊ ┊ ┊ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(insert-character! #\;)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(undo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ ┊ i̶f̶ ┊ i̶s̶ n̶ <̶=̶ 1̶ ┊         ┊ │
│ ┊    ╰           ╯         ┊ │
│ ┊                          ┊ │
│ ┊   1̶                      ┊ │
│ ┊                          ┊ │
│ ┊  ╭     ╭   ╭       ╮ ╮ ╮ ┊ │
│ ┊  ┊ *̶ n̶ ┊ !̶ ┊ -̶ n̶ 1̶ ┊ ┊ ┊ ┊ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(redo!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │    ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(times 2 move-cursor-right!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭    ╭           ╮         ╮ │
│ │ if │ is n <= 1 │         │ │
│ │ ^  ╰           ╯         │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(insert-character! #\;)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭   ╭           ╮          ╮ │
│ │ i̶f̶│ is n <= 1 │          │ │
│ │ ^̶ ╰           ╯          │ │
│ │                          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(times 4 move-cursor-right!)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭   ╭           ╮          ╮ │
│ │ i̶f̶│ is n <= 1 │          │ │
│ │   ╰           ╯          │ │
│ │   ~           ~          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

(insert-character! #\;)

;;(set! verbose #true)

(e.g.
 (snapshot) ===> "
╭        ╭     ╮ ⸾ -> int      ╮
│ define │ ! n │               │
│        ╰     ╯               │
│ ❝┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈•     │
│ ┊ Computes the product ┊     │
│ ┊ 1 * ... * n          ┊     │
│ •┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈❞     │
│ ╭   ╭           ╮          ╮ │
│ │ i̶f̶┊ i̶s̶ n̶ <̶=̶ 1̶ ┊          │ │
│ │   ╰           ╯          │ │
│ │   ~           ~          │ │
│ │   1                      │ │
│ │                          │ │
│ │  ╭     ╭   ╭       ╮ ╮ ╮ │ │
│ │  │ * n │ ! │ - n 1 │ │ │ │ │
╰ ╰  ╰     ╰   ╰       ╯ ╯ ╯ ╯ ╯
")

