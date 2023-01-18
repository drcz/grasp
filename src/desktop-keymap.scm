(import (input))
(define-alias KeyEvent java.awt.event.KeyEvent)

(define (initialize-keymap)
  (set! (key-code-name 0) 'unknown-key)
  
  (set! (key-code-name KeyEvent:VK_F1) 'F1)
  (set! (key-code-name KeyEvent:VK_F2) 'F2)
  (set! (key-code-name KeyEvent:VK_F3) 'F3)
  (set! (key-code-name KeyEvent:VK_F4) 'F4)
  (set! (key-code-name KeyEvent:VK_F5) 'F5)
  (set! (key-code-name KeyEvent:VK_F6) 'F6)
  (set! (key-code-name KeyEvent:VK_F7) 'F7)
  (set! (key-code-name KeyEvent:VK_F8) 'F8)
  (set! (key-code-name KeyEvent:VK_F9) 'F9)
  (set! (key-code-name KeyEvent:VK_F10) 'F10)
  (set! (key-code-name KeyEvent:VK_F11) 'F11)
  (set! (key-code-name KeyEvent:VK_F12) 'F12)

  (set! (key-code-name KeyEvent:VK_0) 0)
  (set! (key-code-name KeyEvent:VK_1) 1)
  (set! (key-code-name KeyEvent:VK_2) 2)
  (set! (key-code-name KeyEvent:VK_3) 3)
  (set! (key-code-name KeyEvent:VK_4) 4)
  (set! (key-code-name KeyEvent:VK_5) 5)
  (set! (key-code-name KeyEvent:VK_6) 6)
  (set! (key-code-name KeyEvent:VK_7) 7)
  (set! (key-code-name KeyEvent:VK_8) 8)
  (set! (key-code-name KeyEvent:VK_9) 9)

  (set! (key-code-name KeyEvent:VK_A) 'a)
  (set! (key-code-name KeyEvent:VK_B) 'b)
  (set! (key-code-name KeyEvent:VK_C) 'c)
  (set! (key-code-name KeyEvent:VK_D) 'd)
  (set! (key-code-name KeyEvent:VK_E) 'e)
  (set! (key-code-name KeyEvent:VK_F) 'f)
  (set! (key-code-name KeyEvent:VK_G) 'g)
  (set! (key-code-name KeyEvent:VK_H) 'h)
  (set! (key-code-name KeyEvent:VK_I) 'i)
  (set! (key-code-name KeyEvent:VK_J) 'j)
  (set! (key-code-name KeyEvent:VK_K) 'k)
  (set! (key-code-name KeyEvent:VK_L) 'l)
  (set! (key-code-name KeyEvent:VK_M) 'm)
  (set! (key-code-name KeyEvent:VK_N) 'n)
  (set! (key-code-name KeyEvent:VK_O) 'o)
  (set! (key-code-name KeyEvent:VK_P) 'p)
  (set! (key-code-name KeyEvent:VK_Q) 'q)
  (set! (key-code-name KeyEvent:VK_R) 'r)
  (set! (key-code-name KeyEvent:VK_S) 's)
  (set! (key-code-name KeyEvent:VK_T) 't)
  (set! (key-code-name KeyEvent:VK_U) 'u)
  (set! (key-code-name KeyEvent:VK_V) 'v)
  (set! (key-code-name KeyEvent:VK_W) 'w)
  (set! (key-code-name KeyEvent:VK_X) 'x)
  (set! (key-code-name KeyEvent:VK_Y) 'y)
  (set! (key-code-name KeyEvent:VK_Z) 'z)

  (set! (key-code-name KeyEvent:VK_LEFT) 'left)
  (set! (key-code-name KeyEvent:VK_RIGHT) 'right)
  (set! (key-code-name KeyEvent:VK_UP) 'up)
  (set! (key-code-name KeyEvent:VK_DOWN) 'down)
  
  (set! (key-code-name KeyEvent:VK_SPACE) 'space)
  (set! (key-code-name KeyEvent:VK_BACK_SPACE) 'backspace)
  (set! (key-code-name KeyEvent:VK_DELETE) 'delete)

  (set! (key-code-name KeyEvent:VK_ENTER) 'enter)
  
  )
