sim[adl_,np_]:=(
If[adl===0,Return[0]];
tut=adl;
ini=Hash[Map[tut[[#,1]]&,Range[Length[tut]]]];
Return[Reap[Do[metti[o,Random[Integer,{1,Length[tut]}]];,{o,1,np}]][[2,1]]]
);

metti[o_,p_]:=(
tut[[p,3]]++;
If[tut[[p,3]]>=tut[[p,4]],val[o,p];];
);

val[o_,p_]:=Module[{cad={p},si,t=0,bu},
si=Flatten[
Reap[
Sow[p];
While[Length[cad]=!=0,
Scan[distribuisci,cad];
cad=Flatten[Reap[Scan[prepara,cad]][[2]]];
cad=DeleteDuplicates[cad];
t++;
Sow[cad];
];
][[2]]];
bu=DeleteDuplicates[si];
Sow[{o,Length[si],Length[bu],t,raggio[bu]}];
];

in[p_]:=tut[[p,3]]++;
prepara[p_]:=Scan[controlla,tut[[p,1]]];
controlla[p_]:=If[tut[[p,3]]>=tut[[p,4]],Sow[p]];
distribuisci[p_]:=(
tut[[p,3]]+=-tut[[p,2]];
Scan[in,tut[[p,1]]];
);

circ[has_,centro_,r_]:=circ[has,centro,r]=cir[centro,r];

cir[centro_,r_]:=Module[{core,pat},
If[r===0,Return[{centro}]];
If[r===-1,Return[{0}]];
core=Flatten[Reap[Scan[Sow[tut[[#,1]]]&,circ[ini,centro,r-1]]][[2]]];
pat=Join[circ[ini,centro,r-1],circ[ini,centro,r-2]];
Return[DeleteDuplicates[pat~Join~core]~Drop~Length[pat]]
];

raggio[val_]:=Module[{r=0,pat,centro=val[[1]]},
pat=Alternatives@@circ[ini,centro,r];
While[MemberQ[val,pat],
r++;
pat=Alternatives@@circ[ini,centro,r];
];
Return[r-1]
];

riga[has_,p_]:=riga[has,p]=rig[p];

rig[p_]:=Module[{l=Length[tut],i=0,r=1,out,ci},
out=ConstantArray[0,l-p];
While[i<(l-p),
ci=circ[ini,p,r];
ci=Pick[ci,UnitStep[ci-p-1],1];
Scan[(out[[#]]=r)&,ci-p];
i+=Length[ci];
r++;
];
Return[out]
];

disz[has_,a_,b_]:=disz[has,a,b]=disz[has,b,a]=
If[a===b,0,riga[has,Min[a,b]][[Abs[a-b]]]];

raggio1[val_]:=Module[{li},
li=Map[(disz[ini,val[[1]],#])&,val];
Return[Max[li]]
];

ret[n_,d_]:=Table[{vic[i,n,d],2*d,0,2*d},{i,1,n^d}];

vic[p_,n_,d_]:=Module[{lis},
lis=Flatten[Reap[
Do[
If[Mod[Ceiling[p/(n^j)],n]=!=0,Sow[p+n^j]];
If[Mod[Ceiling[p/(n^j)],n]=!=1,Sow[p-n^j]];
,{j,0,d-1}
];
][[2]]];
Return[lis]
];

tret[n_,d_,t_,est_:1]:=Module[{ou=ret[n,d],st=Range[1,n^d],sx,dx,r},
If[t>d,Return[0]];
If[n===2,Return[ou]];
Do[
sx=Cases[st,a_Integer/;Mod[Ceiling[a/(n^j)],n]===1];
dx=Cases[st,a_Integer/;Mod[Ceiling[a/(n^j)],n]===0];
Scan[
  (
AppendTo[ou[[sx[[#]],1]],dx[[#]]];
AppendTo[ou[[dx[[#]],1]],sx[[#]]]; 
)& 
,Range[1,Length[sx]]];
,{j,0,t-1}];
Do[
r=Random[Integer,{1,Length[ou]}];
ou[[r,2]]++;
ou[[r,4]]++;
,{est}];
Return[ou]
];

err[V_,E_,est_:1]:=Module[{r,c,lis},
If[E>(V-2)*(V-1)/2,Return[0]];
lis=ret[V,1];
lis[[1,2]]=lis[[1,4]]=lis[[V,4]]=lis[[V,2]]=1;
Do[
r=Random[Integer,{1,V}];
c=Random[Integer,{1,V}];
While[Length[lis[[r,1]]]>=(V-1),r=Random[Integer,{1,V}];];
While[MemberQ[lis[[r,1]],c]||r===c,c=Random[Integer,{1,V}];];
lis[[r,1]]=Append[lis[[r,1]],c];
lis[[r,2]]++;
lis[[r,4]]++;
lis[[c,4]]++;
lis[[c,2]]++;
lis[[c,1]]=Append[lis[[c,1]],r];
,{E}];
Do[
r=Random[Integer,{1,V}];
lis[[r,2]]++;
lis[[r,4]]++;
,{est}];
Return[lis]
];

alr[n_,m_,est_:1]:=Module[{adl={{{},0,0,0}},dove,r},
Do[
dove=Random[Integer,{1,Length[adl]}];
adl=appenditanti[adl,dove,Random[Integer,{1,m}]];
,{n}];
Do[
r=Random[Integer,{1,Length[adl]}];
adl[[r,2]]++;
adl[[r,4]]++;
,{est}];
Return[adl]
];

appendi[adl_,pu_]:=Module[{gr={{pu},1,0,1},ad=adl,l},
l=Length[ad]+1;
AppendTo[ad[[pu,1]],l];
ad[[pu,2]]++;
ad[[pu,4]]++;
Return[Join[ad,{gr}]]
];

appenditanti[adl_,pu_,quanti_]:=Module[{ad=adl},
Do[ad=appendi[ad,pu];,{quanti}];
Return[ad]
];

baa[in_,t_,m_,es_:1]:=Module[{adl=in,lis,r},
If[Length[in]<m,Return[0]];
Do[
lis=dove[adl,m];
adl=Join[adl,{{{},m,0,m}}];
Scan[(adl=connetti[adl,#,Length[adl]])&,lis];
,{t}];
Do[
r=Random[Integer,{1,Length[adl]}];
adl[[r,2]]++;
adl[[r,4]]++;
,{es}];
Return[adl]
];

connetti[adl_,uno_,altro_]:=Module[{ad=adl},
AppendTo[ad[[uno,1]],altro];
ad[[uno,2]]++;
ad[[uno,4]]++;
AppendTo[ad[[altro,1]],uno];
Return[ad]
];

dove[adl_,m_]:=Module[{lis,usc={},p},
lis=Flatten[Map[adl[[#1,1]]&,Range[Length[adl]]]];
Do[
p=RandomChoice[lis];
While[MemberQ[usc,p],p=RandomChoice[lis];];
AppendTo[usc,p];
,{m}];
Return[usc]
];

(*ANALISI DATI*)

plow[adl_,np_,cos_:2]:=Module[{dati,ris},dati=prendi[adl,np];(*analisi power law nei dati generati da sim*)
If[dati==={},Return[0]];
dati=Map[dati[[#,cos]]&,Range[Length[dati]]];
ris=Map[{#,Count[dati,#]}&,Range[Max[dati]]];
ris=DeleteCases[ris,a_List/;a[[2]]===0,1];
Return[ris]
];

estr[sim_,np_,cos_:2]:=Module[{ris,datx=prendi[sim,np]},(*estrae dai dati generati da sim il parametro desiderato fermandosi all'inserimento di np punti*)
If[datx==={},Return[{}]];
ris=Map[datx[[#,cos]]&,Range[Length[datx]]];
Return[ris]
];

degr[adl_]:=Map[Length[adl[[#,1]]]&,Range[Length[adl]]];

prendi[sim_,num_]:=Cases[sim,a_List/;a[[1]]<=num];
