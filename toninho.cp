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

def Node(i,y,n) =
  roll n [x:exists int.CImp]
    (i*(j).i().x*[j].x<->y,
     x*(b).
     case n { val: unr x.x/val.
                   n*(m).x*[2 * m + b].
                   x*(m).n*[m].
                   n*[b].x<->n;
              inc: unr x.x/inc.
                   case x { done: n/done.n*[b].x<->n;
                            carry: [if isZero b
                                    then [n/done.n*[1].x<->n |- n:+{carry:exists int.CImp, done:exists int.CImp}, x:~CImp]
                                    else [n/carry.n*[0].x<->n |- n:+{carry:exists int.CImp, done:exists int.CImp}, x:~CImp]] };
              halt: unr x.x/halt.x().n[].0 }).

check Node(i,x,n) |- i: forall int.bot, x: ~CImp, n:CImp.
check cut [i:exists int.1] (i*[0].i[].0 | Node(i,x,n)) |- x:~CImp,n:CImp.

type Counter = nu X. &{val: exists int.X, inc:X, halt:1}.

def Counter(y,z) =
  roll z [x:CImp]
    (y<->x,
     case z { val: unr x.x/val.
                   x*[0].x*(n).
                   z*[n].z<->x;
              inc: unr x.x/inc.
                   case x { carry: cut [n:CImp]
                                     (cut [i:exists int.1]
                                       (i*[1].i[].0 | Node(i,x,n)) |
                                        z<->n);
                            done: z<->x };
              halt: unr x.x/halt.x().z[].0 }).

check Counter(x,z) |- x:~CImp,z:Counter.


cut [z:CImp]
  (cut [y:CImp]
    (cut [x:CImp] (Epsilon(x) | cut [i:exists int.1] (i*[0].i[].0 | Node(i,x,y))) |
     cut [i:exists int.1] (i*[1].i[].0 | Node(i,y,z))) |
   unr z.z/val.z*[0].z*(i).
   unr z.z/inc.
   case z { carry: unr z.z/val.z*[0].z*(j).
                   unr z.z/halt.z().
                   a*[i].a*[j].a[].0;
            done: unr z.z/val.z*[0].z*(j).
                   unr z.z/halt.z().
                   a*[i].a*[j].a[].0 })
 |- a:exists int.exists int.1.

cut [z:Counter]
  (cut [x:CImp]
     (Epsilon(x) | Counter(x,z)) |
   unr z.z/val.z*(i).
   unr z.z/inc.
   unr z.z/val.z*(j).
   unr z.z/inc.unr z.z/inc.
   unr z.z/val.z*(k).
   unr z.z/halt.z().a*[i].a*[j].a*[k].a[].0)
 |- a:exists int.exists int.exists int.1.
