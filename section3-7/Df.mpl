

Df := module()

option package;

export MM;
local Signature, SortSig;

uses PTools;


Signature := proc( L :: list )
  return mul(-(-1)^nops(p), p in convert(L, 'disjcyc'));
end proc:

SortSig := proc( L :: list )
  local s, p;
  s, p := sort(L, 'output=[sorted, permutation]');
  if mul(s[i-1]-s[i],i=2..nops(s)) = 0 then
    return s, 0;
  else
    return s, Signature(p);
  fi;
end proc;


MM := module ()
  ## On représente l'algèbre [x1, dx1, ...] par [[x1,...], [dx1,...], dx]
  # On représente l'algèbre [x1, dx1, ...] par { d[x_1], ..., d[x_n] }.
  # Les variables doivent être mises dans l'ordre naturel de Maple.

  export Contr, Diff, altMon, Dual, Mul, Normalize, Theta, Expand, UEnc, UDec, IEnc, IDec, VEnc, VDec, HomDfDim;
  local SplitMon, Dual1, Normalize1, Mul1, UDec1, IEnc1, IMon, VDec1, VEncRules, DiffSubs0, DiffSubs, DiffBackSubs ;

  option package;

  altMon := proc( alg )
    option remember;
    if nops([_rest]) > 0 and _rest < 0 then
      return [];
    else
      return map(x -> convert(x, `*`), convert(combinat[choose](alg, _rest), list));
    fi;
  end proc;

  SplitMon := proc(M)
    if M = 1 then
      return NULL;
    elif op(0, M) = `*` then
      return op(M);
    else
      return M;
    fi;
  end proc;

  Normalize1 := proc( L :: list(monomial) )
    local s, sig;
    s, sig := SortSig(L);
    return normal(sig*convert(s, `*`)); 
  end proc;


  Dual1 := proc( M :: monomial, alg )
    local Ms;
    option remember;
    Ms := normal(convert(alg, `*`)/M);
    return SortSig([SplitMon(M), SplitMon(Ms)])[2]*Ms
  end proc:
  Dual := proc(P, alg)
    return MapM(alg, Dual1, P, alg);
  end proc:


  Mul1 := proc( A :: monomial, B :: monomial )
      return Normalize1([SplitMon(A), SplitMon(B)]);
  end proc;
  Mul := proc( P, Q, alg )
    return Expand(BilinMap(alg, Mul1, P, Q), alg);
  end proc;

  Contr := proc( P, Q, alg )
    return Dual(Mul(P, Dual(Q, alg), alg), alg);
  end proc;

  Expand := proc( P, alg )
    return collect( P, alg, 'distributed' );
  end proc:

  Theta := proc(P, alg )
    return Contr( convert(zip(`*`, convert(alg, list), map(op, convert(alg, list))), `+`), P, alg ); 
  end proc;

  #Diff := proc( P, alg )
  #  return Expand(add(Mul(alg[2][i], diff(P, alg[1][i]), alg), i=1..nops(alg[1])), alg);
  #end proc;

  DiffSubs0 := proc( alg )
    option remember;
    return [seq([
      seq(alg[j] = _T_^(3^(j-1)), j=1..i-1),
      alg[i] = 0,
      seq(alg[j] = _T_^(2*3^(j-1)), j=i+1..nops(alg))
      ], i=1..nops(alg))];
  end proc;

  DiffSubs := proc( alg )
    option remember;
    return subs(_T_ = -_T_, DiffSubs0(alg));
  end proc;

  DiffBackSubs := proc(alg)
    option remember;
    return remove(e -> op(1, e) = 0, [seq(op(zip(`=`, subs(DiffSubs0(alg)[i], altMon(alg)[2..-1]), altMon(alg)[2..-1])), i=1..nops(alg))]);
  end proc;

  # Très astucieux !
  Diff := proc( P, alg )
    local R;
    R := map2( diff, P, map(op, convert(alg, list)) );
    R := zip( subs, DiffSubs(alg), R );
    R := subs( DiffBackSubs(alg), R );
    R := zip(`*`, R, convert(alg, list));
    return expand(convert(R, `+`));

  end proc;

  HomDfDim := proc( p, deg, alg )
    if deg < 0 or p < 0 or p > nops(alg) then
      return 0;
    else
      return binomial(nops(alg), p)*binomial(deg+nops(alg)-1, nops(alg)-1);
    end if;
  end proc;

end module:






end module:


