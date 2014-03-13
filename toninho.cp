type CImp = nu X. &{ val: forall int. exists int. X,
                     inc: +{carry: X, done: X},
                     halt: 1}.

def Epsilon(x) =
  roll x [y:1]
    (y[].0,
     case x { val: x*(n).x*[n].y<->x;
              inc: x/carry.y<->x;
              halt: y<->x }).

check Epsilon(x) |- x:CImp.

type Bool = +{t:1, f:1}.
def True(x) = x/t.x[].0.
def False(x)= x/f.x[].0.

def Node(i,y,n) =
  roll n [x:Bool * CImp]
    (x[j].(j <-> i | x <-> y),
     x(b).
     case n { val: unr x.x/val.
                   n*(m).case b { t: b().x*[2*m + 1].x*(m).n*[m].n[b].(True(b) | x<->n);
                                  f: b().x*[2*m].x*(m).n*[m].n[b].(False(b) | x<->n) };
              inc: unr x.x/inc.
                   case x { done: n/done.n[b1].(b <-> b1 | x <-> n);
                            carry: case b { t: b().n/carry.n[b1].(False(b1) | x<->n);
                                            f: b().n/done.n[b1].(True(b1) | x<->n) } };
              halt: case b { t: b().unr x.x/halt.x().n[].0;
                             f: b().unr x.x/halt.x().n[].0 } }).

check Node(i,x,n) |- i:~Bool, x: ~CImp, n:CImp.
check new [i:Bool] (False(i) | Node(i,x,n)) |- x:~CImp,n:CImp.

new [z:CImp]
  (new [y:CImp]
    (new [x:CImp] (Epsilon(x) | new [i:Bool] (False(i) | Node(i,x,y))) |
     new [i:Bool] (True(i) | Node(i,y,z))) |
   unr z.z/val.z*[0].z*(i).
   unr z.z/inc.
   case z { carry: unr z.z/val.z*[0].z*(j).
                   unr z.z/halt.z().
                   a*[i].a*[j].a[].0;
            done: unr z.z/val.z*[0].z*(j).
                   unr z.z/halt.z().
                   a*[i].a*[j].a[].0 })
 |- a:exists int.exists int.1.


type Counter = nu X. &{val: exists int.X, inc:X, halt:1}.

def Counter(z) =
  roll z [x:CImp]
    (Epsilon(x),
     case z { val: unr x.x/val.
                   x*[0].x*(n).
                   z*[n].z<->x;
              inc: unr x.x/inc.
                   case x { carry: new [n:CImp]
                                     (new [i:Bool]
                                       (True(i) | Node(i,x,n)) |
                                        z<->n);
                            done: z<->x };
              halt: unr x.x/halt.x().z[].0 }).
check Counter(z) |- z:Counter.

new [z:Counter]
  (Counter(z) |
   unr z.z/val.z*(i).
   unr z.z/inc.
   unr z.z/val.z*(j).
   unr z.z/inc.unr z.z/inc.
   unr z.z/val.z*(k).
   unr z.z/halt.z().a*[i].a*[j].a*[k].a[].0)
 |- a:exists int.exists int.exists int.1.
