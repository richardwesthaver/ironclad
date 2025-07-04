;;;; idea.lisp -- implementation of the IDEA block cipher

;;; converted mostly from the C code appearing in _Applied Cryptography_
;;; by Bruce Schneier to Common Lisp.  Beware the C-isms.
(in-package :crypto)

(defun idea-mul (a b)
  (declare (type (unsigned-byte 16) a b))
  (cond
    ((zerop a) (ldb (byte 16 0) (- 1 b)))
    ((zerop b) (ldb (byte 16 0) (- 1 a)))
    (t
     (let* ((product (ldb (byte 32 0) (* a b)))
            (x (ldb (byte 16 16) product))
            (y (ldb (byte 16 0) product)))
       (ldb (byte 16 0) (+ (- y x) (if (< y x) 1 0)))))))

(defun idea-mul-inv (x)
  (declare (type (unsigned-byte 16) x))
  (let ((t1 1))
    (declare (type (unsigned-byte 16) t1))
    (when (<= x 1)
      (return-from idea-mul-inv x))
    (multiple-value-bind (t0 y) (truncate 65537 x)
      (declare (type (unsigned-byte 16) t0 y))
      (loop until (= y 1)
        do (let ((q (truncate x y)))
             (declare (type (unsigned-byte 16) q))
             (setf x (mod x y))
             (incf t1 (ldb (byte 16 0) (* q t0)))
             (when (= x 1)
               (return-from idea-mul-inv t1))
             (setf q (truncate y x))
             (setf y (mod y x))
             (incf t0 (ldb (byte 16 0) (* q t1))))
        finally (return (ldb (byte 16 0) (- 1 t0)))))))

(deftype idea-round-keys () '(simple-array (unsigned-byte 16) (52)))

(defun idea-munge-block (input input-start output output-start keys)
  (declare (type (simple-array (unsigned-byte 8) (*)) input output))
  (declare (type (integer 0 #.(- array-dimension-limit 8))
                 input-start output-start))
  (declare (type idea-round-keys keys))
  (with-words ((x1 x2 x3 x4) input input-start :size 2)
    (do ((i 0 (+ i 6)))
        ((>= i 48)
         ;; final round
         (setf x1 (idea-mul x1 (aref keys 48))
               x2 (ldb (byte 16 0) (+ x2 (aref keys 50)))
               x3 (ldb (byte 16 0) (+ x3 (aref keys 49)))
               x4 (idea-mul x4 (aref keys 51)))
         (store-words output output-start x1 x3 x2 x4))
      (setf x1 (idea-mul x1 (aref keys i))
            x2 (ldb (byte 16 0) (+ x2 (aref keys (+ i 1))))
            x3 (ldb (byte 16 0) (+ x3 (aref keys (+ i 2))))
            x4 (idea-mul x4 (aref keys (+ i 3))))
      (let ((t1 x3)
            (t0 x2))
        (setf x3 (idea-mul (logxor x3 x1) (aref keys (+ i 4)))
              x2 (idea-mul (ldb (byte 16 0)
                                (+ (logxor x2 x4) x3))
                           (aref keys (+ i 5))))
        (setf x3 (ldb (byte 16 0) (+ x3 x2))
              x1 (logxor x1 x2)
              x4 (logxor x4 x3)
              x2 (logxor x2 t1)
              x3 (logxor x3 t0))))))

(defclass idea (cipher 8-byte-block-mixin)
  ((encryption-keys :accessor encryption-keys)
   (decryption-keys :accessor decryption-keys)))

(define-block-encryptor idea 8
  (idea-munge-block plaintext plaintext-start ciphertext ciphertext-start
                    (encryption-keys context)))

(define-block-decryptor idea 8
  (idea-munge-block ciphertext ciphertext-start plaintext plaintext-start
                    (decryption-keys context)))

(defun idea-invert-key (encryption-keys decryption-keys)
  (declare (type idea-round-keys encryption-keys decryption-keys))
  (setf (aref decryption-keys 51) (idea-mul-inv (aref encryption-keys 3))
        (aref decryption-keys 50) (ldb (byte 16 0) (- (aref encryption-keys 2)))
        (aref decryption-keys 49) (ldb (byte 16 0) (- (aref encryption-keys 1)))
        (aref decryption-keys 48) (idea-mul-inv (aref encryption-keys 0)))
  (do ((i 1 (1+ i))
       (k 4 (+ k 6))
       (counter 47))
      ((>= i 8)
       (setf (aref decryption-keys 5) (aref encryption-keys 47)
             (aref decryption-keys 4) (aref encryption-keys 46)
             (aref decryption-keys 3) (idea-mul-inv (aref encryption-keys 51))
             (aref decryption-keys 2) (ldb (byte 16 0) (- (aref encryption-keys 50)))
             (aref decryption-keys 1) (ldb (byte 16 0) (- (aref encryption-keys 49)))
             (aref decryption-keys 0) (idea-mul-inv (aref encryption-keys 48)))
       decryption-keys)
    (flet ((set-decryption-key (x)
             (setf (aref decryption-keys counter) x)
             (decf counter)))
      (declare (inline set-decryption-key))
    (set-decryption-key (aref encryption-keys (+ k 1)))
    (set-decryption-key (aref encryption-keys k))
    (set-decryption-key (idea-mul-inv (aref encryption-keys (+ k 5))))
    (set-decryption-key (ldb (byte 16 0) (- (aref encryption-keys (+ k 3)))))
    (set-decryption-key (ldb (byte 16 0) (- (aref encryption-keys (+ k 4)))))
    (set-decryption-key (idea-mul-inv (aref encryption-keys (+ k 2)))))))

(defun idea-key-schedule (key)
  (declare (type (simple-array (unsigned-byte 8) (16)) key))
  (let ((encryption-keys (make-array 52 :element-type '(unsigned-byte 16)))
        (decryption-keys (make-array 52 :element-type '(unsigned-byte 16))))
    (declare (type idea-round-keys encryption-keys decryption-keys))
    (dotimes (i 8)
      (setf (aref encryption-keys i) (ub16ref/be key (* i 2))))
    (do ((j 1 (1+ (mod j 8)))
         (k 8 (1+ k))
         (offset 0))
        ((>= k 52) (values encryption-keys (idea-invert-key encryption-keys
                                                           decryption-keys)))
      (setf (aref encryption-keys (+ j 7 offset))
            (ldb (byte 16 0)
                 (logior (ash (aref encryption-keys (+ (mod j 8) offset)) 9)
                         (ash (aref encryption-keys (+ (mod (1+ j) 8) offset)) -7))))
      (incf offset (if (= j 8) 8 0)))))

(defmethod schedule-key ((cipher idea) key)
  (declare (type (simple-array (unsigned-byte 8) (16)) key))
  (multiple-value-bind (encryption-keys decryption-keys)
      (idea-key-schedule key)
    (setf (encryption-keys cipher) encryption-keys
          (decryption-keys cipher) decryption-keys)
    cipher))

(defcipher idea
  (:encrypt-function idea-encrypt-block)
  (:decrypt-function idea-decrypt-block)
  (:block-length 8)
  (:key-length (:fixed 16)))
