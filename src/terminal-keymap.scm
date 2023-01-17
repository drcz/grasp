(import (input))
(import (term))
(import (match))
(import (infix))

(define (special-key-code key::KeyType)::long
  (bitwise-arithmetic-shift (as long (key:ordinal))
			    java.lang.Integer:SIZE))

(define (regular-key-code c::char)::long
  (as long (char->integer c)))

(define (scancode input::KeyStroke)::long
  (define (with-modifiers code::long)::long
    (bitwise-ior
     (if (input:ctrl-down?) CTRL_MASK 0)
     (if (input:alt-down?) ALT_MASK 0)
     (if (input:shift-down?) SHIFT_MASK 0)
     code))
  
  (match (input:getKeyType)
    (,KeyType:Character
     (let ((c ::java.lang.Character (input:getCharacter)))
       (with-modifiers
	(char->integer
	 (char-downcase
	  (integer->char (c:charValue)))))))
    (type
     (with-modifiers (special-key-code type)))))

(define (input-character input::KeyStroke)::char
  (match (input:getKeyType)
    (,KeyType:Character
     (let* ((c ::java.lang.Character (input:getCharacter)))
      (integer->char (c:charValue))))
    (_
     #\null)))

(define (initialize-keymap)
 
  (set! (key-code-name (special-key-code KeyType:Escape)) 'escape)
  (set! (key-code-name (special-key-code KeyType:Backspace)) 'backspace)
  (set! (key-code-name (special-key-code KeyType:ArrowLeft)) 'left)
  (set! (key-code-name (special-key-code KeyType:ArrowRight)) 'right)
  (set! (key-code-name (special-key-code KeyType:ArrowUp)) 'up)
  (set! (key-code-name (special-key-code KeyType:ArrowDown)) 'down)
  (set! (key-code-name (special-key-code KeyType:Insert)) 'insert)
  (set! (key-code-name (special-key-code KeyType:Delete)) 'delete)
  (set! (key-code-name (special-key-code KeyType:Home)) 'home)
  (set! (key-code-name (special-key-code KeyType:End)) 'end)
  (set! (key-code-name (special-key-code KeyType:PageUp)) 'page-up)
  (set! (key-code-name (special-key-code KeyType:PageDown)) 'page-down)
  (set! (key-code-name (special-key-code KeyType:Tab)) 'tab)
  (set! (key-code-name (special-key-code KeyType:ReverseTab)) 'reverse-tab)
  (set! (key-code-name (special-key-code KeyType:Enter)) 'enter)
  (set! (key-code-name (special-key-code KeyType:F1)) 'F1)
  (set! (key-code-name (special-key-code KeyType:F2)) 'F2)
  (set! (key-code-name (special-key-code KeyType:F3)) 'F3)
  (set! (key-code-name (special-key-code KeyType:F4)) 'F4)
  (set! (key-code-name (special-key-code KeyType:F5)) 'F5)
  (set! (key-code-name (special-key-code KeyType:F6)) 'F6)
  (set! (key-code-name (special-key-code KeyType:F7)) 'F7)
  (set! (key-code-name (special-key-code KeyType:F8)) 'F8)
  (set! (key-code-name (special-key-code KeyType:F9)) 'F9)
  (set! (key-code-name (special-key-code KeyType:F10)) 'F10)
  (set! (key-code-name (special-key-code KeyType:F11)) 'F11)
  (set! (key-code-name (special-key-code KeyType:F12)) 'F12)
  (set! (key-code-name (special-key-code KeyType:F13)) 'F13)
  (set! (key-code-name (special-key-code KeyType:F14)) 'F14)
  (set! (key-code-name (special-key-code KeyType:F15)) 'F15)
  (set! (key-code-name (special-key-code KeyType:F16)) 'F16)
  (set! (key-code-name (special-key-code KeyType:F17)) 'F17)
  (set! (key-code-name (special-key-code KeyType:F18)) 'F18)
  (set! (key-code-name (special-key-code KeyType:F19)) 'F19)
  
  (set! (key-code-name (regular-key-code #\0)) 0)
  (set! (key-code-name (regular-key-code #\1)) 1)
  (set! (key-code-name (regular-key-code #\2)) 2)
  (set! (key-code-name (regular-key-code #\3)) 3)
  (set! (key-code-name (regular-key-code #\4)) 4)
  (set! (key-code-name (regular-key-code #\5)) 5)
  (set! (key-code-name (regular-key-code #\6)) 6)
  (set! (key-code-name (regular-key-code #\7)) 7)
  (set! (key-code-name (regular-key-code #\8)) 8)
  (set! (key-code-name (regular-key-code #\9)) 9)

  (set! (key-code-name (regular-key-code #\a)) 'a)
  (set! (key-code-name (regular-key-code #\b)) 'b)
  (set! (key-code-name (regular-key-code #\c)) 'c)
  (set! (key-code-name (regular-key-code #\d)) 'd)
  (set! (key-code-name (regular-key-code #\e)) 'e)
  (set! (key-code-name (regular-key-code #\f)) 'f)
  (set! (key-code-name (regular-key-code #\g)) 'g)
  (set! (key-code-name (regular-key-code #\h)) 'h)
  (set! (key-code-name (regular-key-code #\i)) 'i)
  (set! (key-code-name (regular-key-code #\j)) 'j)
  (set! (key-code-name (regular-key-code #\k)) 'k)
  (set! (key-code-name (regular-key-code #\l)) 'l)
  (set! (key-code-name (regular-key-code #\m)) 'm)
  (set! (key-code-name (regular-key-code #\n)) 'n)
  (set! (key-code-name (regular-key-code #\o)) 'o)
  (set! (key-code-name (regular-key-code #\p)) 'p)
  (set! (key-code-name (regular-key-code #\q)) 'q)
  (set! (key-code-name (regular-key-code #\r)) 'r)
  (set! (key-code-name (regular-key-code #\s)) 's)
  (set! (key-code-name (regular-key-code #\t)) 't)
  (set! (key-code-name (regular-key-code #\u)) 'u)
  (set! (key-code-name (regular-key-code #\v)) 'v)
  (set! (key-code-name (regular-key-code #\w)) 'w)
  (set! (key-code-name (regular-key-code #\x)) 'x)
  (set! (key-code-name (regular-key-code #\y)) 'y)
  (set! (key-code-name (regular-key-code #\z)) 'z)

  )
