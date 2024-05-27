(* ::Package:: *)

(*
2011.04.25, Created by Wu
2017.04.25, Refactored by Wu
2017.04.26, branch circuit No. in formatUDF[] activated by Wu
2019.10.18, mpc2 and bpa43 data format by Wu
*)


BeginPackage["CaseData`"]

caseData::usage="caseData[name_,optNode_:1,info_:5] UDF, psse_filename, matpower2_filename, or bpa43_filename."


Begin["`Private`"]

tinney2ordering[edge_,vertex_,info_:5]:=Module[{eg,nd,nn,out,itr,num,link,time0},If[info>5,time0=TimeUsed[];];
	eg=Union[Sort[#]&/@Select[edge,#[[1]]!=#[[2]]&]];
	nd=Flatten[eg]//Union;
	nn=Length[nd];If[nn!=vertex,Input[StringForm["Edge & Vertex mismatch! `` - `` = ``. Quit.",vertex,nn,vertex-nn]];Quit[];];
	out=Table[0,{nn}];
	nd=Transpose[{nd,out}];
	For[itr=1,itr<=nn,itr++,
		nd=Sort[{#,Count[Flatten[eg],#]}&/@Sort[nd[[All,1]]],#1[[2]]<=#2[[2]]&];
		num=nd[[1,1]];
		nd=Rest[nd];
		out[[num]]=itr;
		link=Select[eg,#[[1]]==num||#[[2]]==num&];
		eg=DeleteCases[eg,x_/;(x[[1]]==num||x[[2]]==num)];
		If[Length[link]>1,eg=Join[eg,Subsets[Complement[Union[Flatten[link]],{num}],{2}]];];
		];If[info>5,Print["tinney2ordering time used: ",TimeUsed[]-time0,"s"];];
	out
	]

tinney2ordering1[brch_,nbus_,info_:5]:=Module[{mat,nBus,id,out,itr,pos,link,time0},If[info>5,time0=TimeUsed[];];
	mat=({#->1,{#[[2]],#[[1]]}->1}&/@Select[brch,#[[1]]!=#[[2]]&])//Flatten//SparseArray;
	nBus=Length[mat];
	If[nBus!=nbus,Input[StringForm["Branch & nBus mismatch! `` - `` = ``. Quit.",nbus,nBus,nbus-nBus]];Quit[];];
	id=Table[i,{i,nBus}];
	out=Table[0,{nBus}];
	For[itr=1,itr<nBus,itr++,
		pos=Ordering[Total[#]&/@mat,1][[1]];
		out[[id[[pos]]]]=itr;
		link=Most[ArrayRules[mat[[pos,All]]]][[All,1]]//Flatten;
		If[Length[link]>1,(mat[[#[[1]],#[[2]]]]=1;mat[[#[[2]],#[[1]]]]=1;)&/@Subsets[link,{2}];];
		mat=Transpose[Drop[Transpose[Drop[mat,{pos}]],{pos}]];
		id=Drop[id,{pos}];
		];If[info>5,Print["tinney2ordering1 time used: ",TimeUsed[]-time0,"s"];];
	out[[id[[1]]]]=nBus;
	out
	]

tinney2ordering2[brch_,nbus_,info_:5]:=Module[{mat,nBus,id,out,itr,len,pos,tmp,tmp1,tmp2,time0},If[info>5,time0=TimeUsed[];];
	mat=({#->1,{#[[2]],#[[1]]}->1}&/@Select[brch,#[[1]]!=#[[2]]&])//Flatten//SparseArray;
	nBus=Length[mat];If[nBus!=nbus,Input[StringForm["Branch & nBus mismatch! `` - `` = ``. Quit.",nbus,nBus,nbus-nBus]];Quit[];];
	id=Table[i,{i,nBus}];out=Table[0,{nBus}];len=Total[#]&/@mat;itr=1;
	While[itr<nBus,
		pos=Position[len,1]//Flatten;
		If[Length[pos]>0,(tmp=Position[mat[[id[[#]],id]]//Normal,1][[1]];len[[tmp]]-=1;)&/@pos;
			out[[id[[pos]]]]=Range[itr,itr+Length[pos]-1];itr+=Length[pos];tmp=Sort[pos,Greater];id=Fold[Drop[#1,{#2}]&,id,tmp];len=Fold[Drop[#1,{#2}]&,len,tmp];Continue[];];
		pos=Position[len,2]//Flatten;
		If[Length[pos]>0,
			tmp=(tmp1=Position[mat[[id[[#]],id]]//Normal,1]//Flatten;tmp2=id[[tmp1]];If[mat[[tmp2[[1]],tmp2[[2]]]]==1,len[[tmp1]]=len[[tmp1]]-1;#,{}])&/@pos//Flatten;
			If[Length[tmp]>0,out[[id[[tmp]]]]=Range[itr,itr+Length[tmp]-1];itr+=Length[tmp];tmp=Sort[tmp,Greater];id=Fold[Drop[#1,{#2}]&,id,tmp];len=Fold[Drop[#1,{#2}]&,len,tmp];Continue[];];];
		pos=Ordering[len,1][[1]];
		tmp=Position[mat[[id[[pos]],id]]//Normal,1]//Flatten;If[Length[tmp]<2,Print["Warning tinney2ordering2! ",{tmp,id,pos,mat[[id[[pos]]]]//Normal}];];
		({tmp1,tmp2}=id[[#]];If[mat[[tmp1,tmp2]]==0,mat[[tmp1,tmp2]]=1;mat[[tmp2,tmp1]]=1;len[[#]]=len[[#]]+1;];)&/@Subsets[tmp,{2}];
		len[[tmp]]=len[[tmp]]-1;out[[id[[pos]]]]=itr;itr++;id=Drop[id,{pos}];len=Drop[len,{pos}];
		];If[info>5,Print["tinney2ordering2 time used: ",TimeUsed[]-time0,"s"];];
	If[itr==nBus,out[[id[[1]]]]=nBus;];
	out
	]

(************************************************************************************************)

pairString[source_,blank_:"Blank"]:=If[StringQ[source],(If[StringLength[#]==0,blank,#]&/@StringTrim[StringCases[source,"'"~~x___~~"'"->x]])//First,pairString[#,blank]&/@source]

bdglPSSE30Para[data_,list_,str_:0,state_:0,aux_:{}]:=Module[{source,para},If[Length[data]==0,Return[{0,{}}];];
	(*  bus:  I,'NAME',BASKV,IDE,GL,BL,AREA,ZONE,VM,VA,OWNER
		load: I,ID,STATUS,AREA,ZONE,PL,QL,IP,IQ,YP,YQ,OWNER
		gen:  I,ID,PG,QG,QT,QB,VS,IREG,MBASE,ZR,ZX,RT,XT,GTAP,STAT,RMPCT,PT,PB,O1,F1,....O4,F4
		line: I,J,Ckt,R,X,B,RATEA,RATEB,RATEC,GI,BI,GJ,BJ,ST,LEN,O1,F1,...,O4,F4 *)
	If[state==0,source=data;,source=Select[data,(#[[state]]!=0)&];];para=source[[All,list]];
	If[str!=0,para[[All,str]]=pairString[para[[All,str]]];];
	If[Length[aux]>0,para[[All,aux[[1]]]]=para[[All,aux[[1]]]]+source[[All,aux[[2]]]] aux[[3]];];
	{Length[para],para}
	]

xfrmPSSE30Para[data_,nb_]:=Module[{nw2,nw3,para,nbus,buspara,iStar,itr,out,cw,tmp,tmp1,tmp2},If[Length[data]==0,Return[{0,0,0,{},nb,{}}];];
	(*  I,J,K,Ckt,CW,CZ,CM,MAG1,MAG2,NMETR,'NAME',STAT,O1,F1,...,O4,F4
		R1-2,X1-2,SBASE1-2,R2-3,X2-3,SBASE2-3,R3-1,X3-1,SBASE3-1,VMSTAR,ANSTAR
		WINDV1,NOMV1,ANG1,RATA1,RATB1,RATC1,COD1,CONT1,RMA1,RMI1,VMA1,VMI1,NTP1,TAB1,CR1,CX1
		WINDV2,NOMV2,ANG2,RATA2,RATB2,RATC2,COD2,CONT2,RMA2,RMI2,VMA2,VMI2,NTP2,TAB2,CR2,CX2
		WINDV3,NOMV3,ANG3,RATA3,RATB3,RATC3,COD3,CONT3,RMA3,RMI3,VMA3,VMI3,NTP3,TAB3,CR3,CX3 *)
	nw2=nw3=0;nbus=nb;para=buspara=cw={};iStar=99999;itr=1;tmp2={1,3,7,8,9,10,11,12,13};
	While[itr<Length[data],tmp=data[[itr,{3,12}]];If[tmp[[2]]==0,If[tmp[[1]]==0,itr+=4;,itr+=5;];Continue[];];
		out=Flatten[{data[[itr,{1,2,3,8,9}]],pairString[data[[itr,{4,11}]],"xfrm"],999.9,-999.9}];
		If[data[[itr,6]]!=1,Print["Warning: CZ\[NotEqual]1 hence Rz/Xz not per unit ",out];];
		If[data[[itr,7]]!=1,Print["Warning: CM\[NotEqual]1 hence Gm/Bm not per unit ",out];];
		If[tmp[[1]]==0,
			tmp1=Flatten[{data[[itr+1,{1,2}]],data[[itr+2,tmp2]],data[[itr+3,1]]}];
			tmp1[[3]]/=tmp1[[12]];tmp1[[{1,2}]]*=tmp1[[12]]^2;
			AppendTo[para,Flatten[Insert[out[[{1,2,6,4,5,7,8,9}]],tmp1[[{1,2,3,4,5,7,8,11,6,9,10}]],4]]];AppendTo[cw,data[[itr,5]]];nw2++;itr+=4;,
			(* Xfrm format:  numI numJ I J Ckt R X Tk Ta Ttype Tmax Tmin Tap Ireg Cmax Cmin G B Name Pmax Pmin *)(* k:1+Z+GB *)
			nbus++;iStar++;tmp1=data[[itr+1,{10,11}]];AppendTo[out,iStar];
			AppendTo[buspara,{nbus,iStar,"XfrmStar",1,1,99,0,0,tmp1[[1]],tmp1[[2]],1.2,0.8}];
			tmp1={#[[1]]+#[[3]]-#[[2]],#[[1]]+#[[2]]-#[[3]],#[[2]]+#[[3]]-#[[1]]}&[Partition[data[[itr+1,{1,2,4,5,7,8}]],2]];
			tmp1=Join[tmp1,data[[{itr+2,itr+3,itr+4},tmp2]],2];
			AppendTo[para,Flatten[Insert[out[[{1,10,6,4,5,7,8,9}]],tmp1[[1,{1,2,3,4,5,7,8,11,6,9,10}]],4]]];
			AppendTo[para,Flatten[Insert[out[[{2,10,6,8,9,7,8,9}]],tmp1[[2,{1,2,3,4,5,7,8,11,6,9,10}]],4]]];
			AppendTo[para,Flatten[Insert[out[[{3,10,6,8,9,7,8,9}]],tmp1[[3,{1,2,3,4,5,7,8,11,6,9,10}]],4]]];
			cw=Join[cw,Table[If[data[[itr,5]]==2,3,data[[itr,5]]],{3}]];nw3++;itr+=5;];];
	{Length[para],nw2,nw3,para,cw,nbus,buspara}
	]

casePSSE30[file_,info_:5]:=Module[{rawData,endPos,sBase,tmp,tmp1,tmp2,tmp3,fileOPF,pos1,pos2,nBus,busPara,busPosAssoc,nLoad,loadPara,nGen,genPara,nLine,linePara,nXfrm,nXfrm2,nXfrm3,xfrmPara},
	Print["Case PSSE30 PF file name: ",file];
	rawData=Import[file,"CSV",CharacterEncoding->"CP936"];
	endPos=MapIndexed[If[StringQ[#1],If[StringFreeQ[#1,"END",IgnoreCase->True],{},#2],{}]&,rawData[[All,1]]]//Flatten;
	sBase=If[StringQ[#],ImportString[#,"Table"][[1,1]],#]&/@rawData[[1,2]];
	(* Bus format:  num I name type Vbase area GL BL V A Vmax Vmin *)
	busPara=rawData[[Range[4,endPos[[1]]-1]]];
	{nBus,busPara}=bdglPSSE30Para[busPara,{1,2,4,3,8,5,6,9,10},2,0,{5,7,100}];
	busPara=Join[Table[{i},{i,nBus}],busPara,Table[{1.1,0.9},{nBus}],2];
	busPosAssoc=AssociationThread[busPara[[All,2]]->busPara[[All,1]]];
	busPara[[All,{7,8}]]/=sBase;
	(* Load format: num I ID PL QL IP IQ YP YQ *)
	loadPara=rawData[[Range[endPos[[1]]+1,endPos[[2]]-1]]];
	{nLoad,loadPara}=bdglPSSE30Para[loadPara,{1,2,6,7,8,9,10,11},2,3];
	If[nLoad>0,tmp={busPosAssoc[#]}&/@loadPara[[All,1]];
		loadPara=Join[tmp,loadPara,2];loadPara[[All,{4,5,6,7,8,9}]]/=sBase;
	];
	(* Gen format:  num I ID PG QG Vset Ireg Qmax Qmin Pmax Pmin a b c *)
	genPara=rawData[[Range[endPos[[2]]+1,endPos[[3]]-1]]];
	{nGen,genPara}=bdglPSSE30Para[genPara,{1,2,3,4,7,8,5,6,17,18},2,15];
	tmp={busPosAssoc[#]}&/@genPara[[All,1]];
	genPara=Join[tmp,genPara,Table[{1,2,3},{nGen}],2];
	genPara[[All,{4,5,8,9,10,11}]]/=sBase;
	tmp=Count[(#[[8]]==#[[9]])&/@genPara,True];If[tmp>0,Print["Warning! ",tmp," gens have Qgmax = Qgmin"];];
	(* Line format:  numI numJ I J Ckt R X B Pmax Pmin *)
	linePara=rawData[[Range[endPos[[3]]+1,endPos[[4]]-1]]];
	{nLine,linePara}=bdglPSSE30Para[linePara,{1,2,3,4,5,6},3,14];
	If[nLine>0,linePara[[All,2]]=Abs[linePara[[All,2]]];(* negative for metering end *)
		tmp1={busPosAssoc[#]}&/@linePara[[All,1]];tmp2={busPosAssoc[#]}&/@linePara[[All,2]];
		linePara=Join[tmp1,tmp2,linePara,Table[{999.9,-999.9},{nLine}],2];linePara[[All,8]]/=2;(* Total B to B/2 *)
	];
	(* Xfrm format:  numI numJ I J Ckt R X Tk Ta Ttype Tmax Tmin Tap Ireg Cmax Cmin G B Name Pmax Pmin *)(* k:1+Z+GB *)
	xfrmPara=rawData[[Range[endPos[[4]]+1,endPos[[5]]-1]]];
	{nXfrm,nXfrm2,nXfrm3,xfrmPara,tmp3,nBus,tmp}=xfrmPSSE30Para[xfrmPara,nBus];
	If[nXfrm>0,xfrmPara[[All,7]]*=Degree;If[Length[tmp]>0,busPara=Join[busPara,tmp];];
		tmp1={busPosAssoc[#]}&/@xfrmPara[[All,1]];tmp2={busPosAssoc[#]}&/@xfrmPara[[All,2]];
		xfrmPara=Join[tmp1,tmp2,xfrmPara,2];
		tmp1=Position[tmp3,2]//Flatten;If[Length[tmp1]>0,xfrmPara[[tmp1,{6,7}]]/=busPara[[xfrmPara[[tmp1,2]],5]]^2;xfrmPara[[tmp1,8]]*=busPara[[xfrmPara[[tmp1,2]],5]]/busPara[[xfrmPara[[tmp1,1]],5]];];
		tmp1=Position[tmp3,3]//Flatten;If[Length[tmp1]>0,xfrmPara[[tmp1,8]]/=busPara[[xfrmPara[[tmp1,1]],5]];];
	];
	(* opf data *)
	fileOPF=StringReplace[file,".raw"->".rop"];
	If[FileExistsQ[fileOPF],Print["Case PSSE OPF file name: ",fileOPF];
		rawData=Import[fileOPF,"CSV",CharacterEncoding->"CP936"];
		endPos=MapIndexed[If[StringQ[#1],If[StringFreeQ[#1,"END",IgnoreCase->True],{},#2],{}]&,rawData[[All,1]]]//Flatten;
		(* Bus format:  num I name type Vbase area GL BL V A Vmax Vmin *)
		tmp=rawData[[Range[2,endPos[[1]]-1]]];{tmp1,tmp2}=bdglPSSE30Para[tmp,{1,2,3}];tmp=Intersection[busPara[[All,2]],tmp2[[All,1]]];
		pos1=busPosAssoc[#]&/@tmp;pos2=Flatten[Position[tmp2[[All,1]],#]&/@tmp];
		busPara[[pos1,{11,12}]]=tmp2[[pos2,{2,3}]];
		(* Gen format:  num I ID PG QG Vset Ireg Qmax Qmin Pmax Pmin a b c *)
		tmp=rawData[[Range[endPos[[4]]+1,endPos[[5]]-1]]];{tmp1,tmp2}=bdglPSSE30Para[tmp,{1,2,4},2];
		tmp=Intersection[genPara[[All,{2,3}]],tmp2[[All,{1,2}]]];
		pos1=Flatten[Position[genPara[[All,{2,3}]],#]&/@tmp];pos2=Flatten[Position[tmp2[[All,{1,2}]],#]&/@tmp];tmp2=tmp2[[pos2]];
		tmp=rawData[[Range[endPos[[5]]+1,endPos[[6]]-1]]];{tmp1,tmp3}=bdglPSSE30Para[tmp,{1,7}];
		tmp=Intersection[tmp2[[All,3]],tmp3[[All,1]]];
		pos2=Flatten[Position[tmp2[[All,3]],#]&/@tmp];pos1=pos1[[pos2]];
		pos2=Flatten[Position[tmp3[[All,1]],#]&/@tmp];tmp2=tmp3[[pos2]];
		tmp=rawData[[Range[endPos[[11]]+1,endPos[[12]]-1]]];{tmp1,tmp3}=bdglPSSE30Para[tmp,{1,3,4,5}];
		tmp=Intersection[tmp2[[All,2]],tmp3[[All,1]]];
		pos2=Flatten[Position[tmp2[[All,2]],#]&/@tmp];pos1=pos1[[pos2]];
		pos2=Flatten[Position[tmp3[[All,1]],#]&/@tmp];tmp2=tmp3[[pos2]];
		genPara[[pos1,{12,13,14}]]=tmp2[[All,{2,3,4}]];
		(* Line format:  numI numJ I J Ckt R X B *)
		tmp=rawData[[Range[endPos[[13]]+1,endPos[[14]]-1]]];{tmp1,tmp2}=bdglPSSE30Para[tmp,{1,2,3,5,6},3];
		If[nLine>0,
			tmp=Intersection[linePara[[All,{3,4,5}]],tmp2[[All,{1,2,3}]]];
			pos1=Flatten[Position[linePara[[All,{3,4,5}]],#]&/@tmp];pos2=Flatten[Position[tmp2[[All,{1,2,3}]],#]&/@tmp];
			linePara[[pos1,{9,10}]]=tmp2[[pos2,{4,5}]]/sBase;
			tmp=Intersection[linePara[[All,{3,4,5}]],tmp2[[All,{2,1,3}]]];
			pos1=Flatten[Position[linePara[[All,{3,4,5}]],#]&/@tmp];pos2=Flatten[Position[tmp2[[All,{2,1,3}]],#]&/@tmp];
			linePara[[pos1,{9,10}]]=tmp2[[pos2,{5,4}]]/sBase;
		];
		(* Xfrm format:  numI numJ I J Ckt R X Tk Ta Ttype Tmax Tmin Tap Ireg Cmax Cmin G B Name Pmax Pmin *)(* k:1+Z+GB *)
		If[nXfrm>0,
			tmp=Intersection[xfrmPara[[All,{3,4,5}]],tmp2[[All,{1,2,3}]]];
			pos1=Flatten[Position[xfrmPara[[All,{3,4,5}]],#]&/@tmp];pos2=Flatten[Position[tmp2[[All,{1,2,3}]],#]&/@tmp];
			xfrmPara[[pos1,{20,21}]]=tmp2[[pos2,{4,5}]]/sBase;
			tmp=Intersection[xfrmPara[[All,{3,4,5}]],tmp2[[All,{2,1,3}]]];
			pos1=Flatten[Position[xfrmPara[[All,{3,4,5}]],#]&/@tmp];pos2=Flatten[Position[tmp2[[All,{2,1,3}]],#]&/@tmp];
			xfrmPara[[pos1,{20,21}]]=tmp2[[pos2,{5,4}]]/sBase;
		];
	];
	(* Tinney2 node ordering *)
	If[optNodeLoc==1,tmp=tinney2ordering2[Join[If[nLine>0,linePara[[All,{1,2}]],{}],If[nXfrm>0,xfrmPara[[All,{1,2}]],{}]],nBus,info];
		busPara[[All,1]]=tmp[[busPara[[All,1]]]];genPara[[All,1]]=tmp[[genPara[[All,1]]]];
		If[nLoad>0,loadPara[[All,1]]=tmp[[loadPara[[All,1]]]];];
		If[nLine>0,linePara[[All,1]]=tmp[[linePara[[All,1]]]];linePara[[All,2]]=tmp[[linePara[[All,2]]]];];
		If[nXfrm>0,xfrmPara[[All,1]]=tmp[[xfrmPara[[All,1]]]];xfrmPara[[All,2]]=tmp[[xfrmPara[[All,2]]]];];
	];
	tmp=Sort[Transpose[{Range[nBus],busPara[[All,1]]}],#1[[2]]<#2[[2]]&];tmp1=tmp[[All,1]];
	(*Print[MatrixForm[{{"nBus",nBus},{"nLoad",nLoad},{"nGen",nGen},{"nLine",nLine},{"nXfrm",{nXfrm,{nXfrm2,nXfrm3}}}}]];
	Print[MatrixForm[busPara]];Print[MatrixForm[loadPara]];Print[MatrixForm[genPara]];Print[MatrixForm[linePara]];Print[MatrixForm[xfrmPara]];*)
	{busPara,loadPara,genPara,linePara,Select[xfrmPara,#[[9]]==0&],Select[xfrmPara,#[[9]]!=0&],{},{},tmp1,busPara[[tmp1,2]]}
	]

(************************************************************************************************)

caseMpc2[file_,info_:5]:=Module[{mpc2Trm,tmp,tmp1,tmp2,baseMVA,pos,data,busPosAssoc,nBus,busPara,nLoad,loadPara,nGen,genPara,errName,nLine,linePara,nXfrm,xfrmPara},
	Print["Case Matpower2 PF file name : ",file];
	tmp=Select[Import[file,{"Text","Lines"}],StringLength[#]>1&&!StringContainsQ[#,RegularExpression["\\A%(?s).*"]]&];
	tmp1=SelectFirst[tmp,StringContainsQ[#,"mpc.version"~~__~~"'2'"]&];
	If[Head[tmp1]===Missing,Print["Not mpc version 2! Quit."];Quit[];];
	tmp1=SelectFirst[tmp,StringContainsQ[#,"mpc.baseMVA"]&];
	tmp2=Table[StringPosition[tmp1,i][[1,2]],{i,{"=",";"}}]//Flatten;
	baseMVA=StringTake[tmp1,{tmp2[[1]]+1,tmp2[[2]]-1}]//ToExpression;
	tmp1=Table[pos=FirstPosition[tmp,str_String/;StringContainsQ[str,i]];If[Head[pos]===Missing,{},pos],{i,{"mpc.bus ","mpc.gen ","mpc.branch ","mpc.gencost "}}]+1//Flatten;
	tmp2=Position[StringContainsQ[#,"];"]&/@tmp,True]-1//Flatten;
	If[Length[tmp1]<3,Print[StringForm["Quit! Check data pairs : { `` , `` }",tmp1,tmp2]];Quit[];];
	If[Length[tmp1]!=Length[tmp2],pos=Table[Cases[tmp2,x_Integer/;x>i][[1]],{i,tmp1}];Print["Warning! Auto match pairs ",{tmp1,tmp2}," to ",{tmp1,pos}]];
	pos={tmp1,tmp2}//Transpose;tmp1=Ordering[pos[[All,1]]];tmp2=pos[[tmp1]]//Flatten;
	If[!And@@Thread[Differences[tmp2]>=0],Print["Quit! Check data pairs : "<>ToString[pos]];Quit[];];
	mpc2Trm=StringTrim[#,";"]&/@tmp;

	(* mpc.bus : num type Pd Qd Gs Bs area V A Vbase zone Vmax Vmin (type=4 isolate) *)
	tmp=ImportString[Riffle[mpc2Trm[[#[[1]];;#[[2]]]],Table["\n",{#[[2]]-#[[1]]+1}]]//StringJoin,"Table"]&[pos[[1]]];
	If[Length[(Dimensions[#]&/@tmp)//Union]>1 || Length[tmp[[1]]]<13,Print["Warning! Dimension inconsist : mpc.bus"];];
	data=Select[tmp,#[[2]]!=4&];nBus=data//Length;
	busPara=Join[Table[{i},{i,nBus}],data[[All,{1,1,2,10,7}]],data[[All,{5,6}]]/baseMVA//N,data[[All,{8,9,12,13}]],2];
	busPosAssoc=AssociationThread[busPara[[All,2]]->busPara[[All,1]]];
	(* Bus format:  num I name type Vbase area GL BL V A Vmax Vmin *)
	tmp=Select[Join[Partition[busPara[[All,1]],1],data,2],#[[4]]!=0||#[[5]]!=0&];nLoad=tmp//Length;
	loadPara=If[nLoad>0,Join[tmp[[All,{1,2}]],Table[{1},{nLoad}],tmp[[All,{4,5}]]/baseMVA//N,Table[{0,0,0,0},{nLoad}],2],{}];
	If[nLoad>Length[loadPara[[All,1]]//Union],Print["Warning! Multiple load at one bus ",{nLoad,Length[loadPara[[All,1]]//Union]}];];
	(* Load format:  num I ID PL QL IP IQ YP YQ *)

	(* mpc.gen : num Pg Qg Qmax Qmin Vg Sbase status Pmax Pmin Pc1 Pc2 Qc1min Qc1max Qc2min Qc2max Ragc R10 R30 R2 (status\[LessEqual]0 out) *)
	tmp=ImportString[Riffle[mpc2Trm[[#[[1]];;#[[2]]]],Table["\n",{#[[2]]-#[[1]]+1}]]//StringJoin,"Table"]&[pos[[2]]];
	If[Length[(Dimensions[#]&/@tmp)//Union]>1 || Length[tmp[[1]]]<21,Print["Warning! Dimension inconsist : mpc.gen"];];
	data=Table[{1,2,3},{Length[tmp]}];(* mpc.gencost : model start shut n+1 cn....c0 (model=1 piecewise 2 polynomial) *)
	If[Length[pos]>3,tmp1=ImportString[Riffle[mpc2Trm[[#[[1]];;#[[2]]]],Table["\n",{#[[2]]-#[[1]]+1}]]//StringJoin,"Table"]&[pos[[4]]];
	If[Length[tmp1]!=Length[tmp],Print["Warning! Dimension inconsist : mpc.gencost"];,
	data=If[#[[1]]==2&&#[[4]]>=3,#[[{5,6,7}]],{1,2,3}]&/@tmp1;];];
	data=Select[Join[tmp,data,2],#[[8]]>0&];nGen=data//Length;tmp1={busPosAssoc[#]}&/@data[[All,1]];
	genPara=Join[tmp1,data[[All,{1}]],Table[{1},{nGen}],data[[All,{2,3}]]/baseMVA//N,data[[All,{6}]],Table[{0},{nGen}],(data[[All,{4,5,12,11}]]/baseMVA/.{"Inf"->10^6,"-Inf"->-10^6})//N,data[[All,{22,23,24}]],2];
	If[nGen>Length[genPara[[All,1]]//Union],Print["Quit! Multiple gen at one bus ",{nGen,Length[genPara[[All,1]]//Union]}];Quit[];];
	tmp1=Position[busPara[[All,4]],3]//Flatten;If[Length[tmp1]!=1,Print["Error! Inadequate slack bus ",busPara[[tmp1]]//MatrixForm];Quit[];];
	tmp2=Position[genPara[[All,1]],tmp1[[1]]]//Flatten;If[Length[tmp2]!=1,Print[StringForm["Error! Slack bus `` vs gen ``",tmp1,genPara[[tmp2,2]]]];Quit[];];
	tmp2=Position[busPara[[All,4]],2]//Flatten;If[Length[tmp2]>=nGen,Print["Warning! More pvBus than gen ",{busPara[[tmp2]]//Length,nGen}];];
	If[!SubsetQ[genPara[[All,1]],tmp2],tmp=Complement[tmp2,Intersection[Join[tmp2,tmp1],genPara[[All,1]]]];Print["Warning! Reset pvbus without gen to pqbus ",tmp];(busPara[[#,4]]=1;)&/@tmp;];
	tmp=Count[(#[[8]]==#[[9]])&/@genPara,True];If[tmp>0,Print["Warning! ",tmp," gens have Qgmax = Qgmin"];];
	(* Gen format:  num I ID PG QG Vset Ireg Qmax Qmin Pmax Pmin a b c *)

	(* mpc.branch : from to r x b Rlong Rshort Rem tap shift status Admin Admax (b total charging;tap=0 line;status=0 out) *)
	tmp=ImportString[Riffle[mpc2Trm[[#[[1]];;#[[2]]]],Table["\n",{#[[2]]-#[[1]]+1}]]//StringJoin,"Table"]&[pos[[3]]];
	If[Length[(Dimensions[#]&/@tmp)//Union]>1 || Length[tmp[[1]]]<13,Print["Warning! Dimension inconsist : mpc.branch"];];
	data=Select[tmp,#[[11]]==1&];
	(* Line format:  numI numJ I J Ckt R X B Pmax Pmin *)
	tmp=Select[data,#[[9]]==0&];nLine=tmp//Length;linePara={};
	If[nLine>0,errName={};tmp1=(tmp2=busPosAssoc[#];If[Head[tmp2]===Missing,AppendTo[errName,#];{-1},{tmp2}])&/@Join[tmp[[All,1]],tmp[[All,2]]];If[Length[errName]>0,Print["Error! line name : ",Length[errName]];Print[errName//Union];(*Quit[];*)];
		linePara=Join[tmp1[[;;nLine]],tmp1[[nLine+1;;]],tmp[[All,{1,2}]],Table[{0},{nLine}],tmp[[All,{3,4}]],tmp[[All,{5}]]/2,tmp[[All,{6}]]/baseMVA//N,-tmp[[All,{6}]]/baseMVA//N,2];];
	(* Xfrm format:  numI numJ I J Ckt R X Tk Ta Ttype Tmax Tmin Tap Ireg Cmax Cmin G B Name Pmax Pmin *)(* k:1+Z+GB *)
	tmp=Select[data,#[[9]]!=0&];nXfrm=tmp//Length;xfrmPara={};
	If[nXfrm>0,errName={};tmp1=(tmp2=busPosAssoc[#];If[Head[tmp2]===Missing,AppendTo[errName,#];{-1},{tmp2}])&/@Join[tmp[[All,1]],tmp[[All,2]]];If[Length[errName]>0,Print["Error! xfrm name : ",Length[errName]];Print[errName//Union];(*Quit[];*)];
		xfrmPara=Join[tmp1[[;;nXfrm]],tmp1[[nXfrm+1;;]],tmp[[All,{1,2}]],Table[{0},{nXfrm}],tmp[[All,{3,4}]],tmp[[All,{9}]],tmp[[All,{10}]]Degree,Table[Table[0,{10}],{nXfrm}],tmp[[All,{6}]]/baseMVA//N,-tmp[[All,{6}]]/baseMVA//N,2];];
	
	(* Tinney2 node ordering *)
	If[optNodeLoc==1,tmp=tinney2ordering2[Join[If[nLine>0,linePara[[All,{1,2}]],{}],If[nXfrm>0,xfrmPara[[All,{1,2}]],{}]],nBus,info];
		busPara[[All,1]]=tmp[[busPara[[All,1]]]];genPara[[All,1]]=tmp[[genPara[[All,1]]]];
		If[nLoad>0,loadPara[[All,1]]=tmp[[loadPara[[All,1]]]];];
		If[nLine>0,linePara[[All,1]]=tmp[[linePara[[All,1]]]];linePara[[All,2]]=tmp[[linePara[[All,2]]]];];
		If[nXfrm>0,xfrmPara[[All,1]]=tmp[[xfrmPara[[All,1]]]];xfrmPara[[All,2]]=tmp[[xfrmPara[[All,2]]]];];
	];
	tmp=Sort[Transpose[{Range[nBus],busPara[[All,1]]}],#1[[2]]<#2[[2]]&];tmp1=tmp[[All,1]];
	(*Print[MatrixForm[{{"nBus",nBus},{"nLoad",nLoad},{"nGen",nGen},{"nLine",nLine},{"nXfrm",{nXfrm,{nXfrm2,nXfrm3}}}}]];
	Print[MatrixForm[busPara]];Print[MatrixForm[loadPara]];Print[MatrixForm[genPara]];Print[MatrixForm[linePara]];Print[MatrixForm[xfrmPara]];*)
	{busPara,loadPara,genPara,linePara,Select[xfrmPara,#[[9]]==0&],Select[xfrmPara,#[[9]]!=0&],{},{},tmp1,busPara[[tmp1,2]]}
	]

(************************************************************************************************)

chsCodeConvert[str_]:=Module[{char,pos},
	char=ToCharacterCode[str];pos=FirstPosition[char,x_/;x>127];
	If[Head[pos]===Missing,str,chsChar++;FromCharacterCode[char,"MacintoshChineseSimplified"]]
	]

caseBpa43[file_,info_:5]:=Module[{bpaData,tmp,tmp1,tmp2,tmp3,baseMVA,data,busPosAssoc,errName,busSep,nBus,busPara,nLoad,loadPara,nGen,genPara,lineSep,nLine,linePara,xfrmSep,nXfrm,xfrmPara},
	Print["Case BPA43 PF file name : ",file];
	bpaData=Select[Import[file,{"Text","Lines"}],StringLength[#]>1&&!StringStartsQ[#,"."]&];
	tmp1=SelectFirst[bpaData,StringContainsQ[#,"MVA_BASE"]&];
	baseMVA=If[Head[tmp1]===Missing,100,tmp2=Table[StringPosition[tmp1,i][[1,2]],{i,{"=","\\"}}]//Flatten;StringTake[tmp1,{tmp2[[1]]+1,tmp2[[2]]-1}]//ToExpression]//N;
	chsChar=0;(* import CharacterEncoding\[Rule]"MacintoshChineseSimplified" *)

	(* B card: 
	1(1A1:B) (2A1:_/PQ,Q/PV,S/slack,E/PVnolimit,other/warning) (3A1) (4-6A3) 
	2(7-14A8:name)
	3(15-18F4.0:kVbase)
	4(19-20A2:areaName) 
	56(21-30F5.0*2:Pl,Ql) 
	78(31-38F4.0*2:G,B/+Cap) 
	9(39-42F4.0:Pmax) 
	10(43-47F5.0:Pg) 
	11(48-52F5.0:Qgmax4PV,Qg4PQ) 
	12(53-57F5.0:Qgmin) 
	13(58-61F4.3:Vg/PV,Vmax/pu) 
	14(62-65F4.3:Vmin/pu,angl/slackF4.1) 
	15(66-67A8+F4.0) (78-80F3.0)*)
	busSep={7,15,19,21,26,31,35,39,43,48,53,58,62,66};
	tmp=Select[bpaData,StringStartsQ["B"]];nBus=tmp//Length;
	tmp3=Switch[StringTake[#,{2}]," ",1,x_/;x=="Q"||x=="E",2,"S",3,_,StringTake[#,2]]&/@tmp;
	tmp1=Position[tmp3,_?StringQ]//Flatten;
	If[Length[tmp1]>0,Print["Error! Unhandle type of bus : ",tmp3[[tmp1]]//Union];(*Quit[];,*)
		tmp1=Complement[Range[nBus],tmp1];tmp=tmp[[tmp1]];tmp3=tmp3[[tmp1]];nBus=tmp//Length;];
	tmp1=StringInsert[(tmp2=StringLength[#];Which[tmp2<66,StringPadRight[#,66," "],tmp2>80,StringTake[#,{1,80}],True,#]),",",busSep]&/@tmp;
	data=ImportString[Riffle[tmp1,Table["\n",{nBus}]]//StringJoin,{"CSV","RawData"}];data=Join[data,Table[{0,0,1,i},{i,nBus}],2];
	data[[All,2]]=chsCodeConvert[#]&/@data[[All,2]];
	tmp2=Prepend[Range[5,14],3];
	data[[All,tmp2]]=ToExpression[data[[All,tmp2]]/.{""->0,"."->0}];
	data[[All,5;;12]]/=baseMVA;
	data[[All,{13,14}]]=Map[If[#<100,#,#/1000.]&,data[[All,{13,14}]],{2}];
	data[[All,16]]=tmp3;
	tmp2=Position[data[[All,16]],3]//Flatten;If[Length[tmp2]!=1,Print["Error! Inadequate slack bus : ",data[[tmp2,2]]]; (*Quit[];*)];
	If[nBus>Length[data[[All,2]]//Union],Print["Error! Duplicate bus name : ",{nBus,Length[data[[All,2]]//Union]}];(*Quit[];*)];

	(* Bus format:  num I name type Vbase area GL BL V A Vmax Vmin *)
	busPara=data[[All,{19,19,2,16,3,4,7,8,13,14,13,14}]];
	busPosAssoc=AssociationThread[busPara[[All,3]]->Range[nBus]];
	(* Load format:  num I ID PL QL IP IQ YP YQ *)
	tmp=Select[data,#[[5]]!=0||#[[6]]!=0&];nLoad=tmp//Length;
	loadPara=If[nLoad>0,tmp[[All,{19,19,18,5,6,17,17,17,17}]],{}];
	(* Gen format:  num I ID PG QG Vset Ireg Qmax Qmin Pmax Pmin a b c *)
	tmp=Select[data,#[[10]]!=0||(#[[11]]!=0&&#[[16]]==1)||#[[16]]==2||#[[16]]==3&];nGen=tmp//Length;
	genPara=Join[tmp[[All,{19,19,18,10,11,13,17,11,12,9,17,18}]],2tmp[[All,{18}]],3tmp[[All,{18}]],2];
	tmp2=Count[(#[[8]]==#[[9]])&/@genPara,True];If[tmp2>0,Print["Warning! ",tmp2," gens have Qgmax = Qgmin"];];

	(* L card: 
	1(1A1:L) (2A1) (3A1) (4-6A3) 
	2(7-14A8:name1)
	3(15-18F4.0:kVbase1) (19I1) 
	4(20-27A8:name2)
	5(28-31F4.0:kVbase2) (32A1:Ckt) (34-37F4.0) (38I1) 
	67(39-50F6.5*2:R,X) 
	89(51-62F6.5*2:G/2,B/2) 
	10(63-66F4.1) (67-74A8) (75-77A1+I2) (78-80A1+I2) *)
	lineSep={7,15,20,28,39,45,51,57,63};
	tmp=Select[bpaData,StringStartsQ["L"]];nLine=tmp//Length;linePara={};
	If[nLine>0,
		tmp3=If[StringTake[#,{2}]==" ",1,StringTake[#,2]]&/@tmp;
		tmp1=Position[tmp3,_?StringQ]//Flatten;
		If[Length[tmp1]>0,Print["Error! Unhandle type of line : ",tmp3[[tmp1]]//Union];(*Quit[];*)
			tmp=tmp[[Complement[Range[nLine],tmp1]]];nLine=tmp//Length;];
		tmp1=StringInsert[(tmp2=StringLength[#];Which[tmp2<63,StringPadRight[#,63," "],tmp2>80,StringTake[#,{1,80}],True,#]),",",lineSep]&/@tmp;
		data=ImportString[Riffle[tmp1,Table["\n",{nLine}]]//StringJoin,{"CSV","RawData"}];data=Join[data,Table[{1,999,-999},{nLine}],2];If[chsChar>0,data[[All,2]]=chsCodeConvert[#]&/@data[[All,2]];data[[All,4]]=chsCodeConvert[#]&/@data[[All,4]];];
		data[[All,6;;9]]=Map[If[#<100000,#,#/100000.]&,ToExpression[data[[All,6;;9]]/.{""->0,"."->0}],{2}];
		errName={};tmp1=(tmp2=busPosAssoc[#];If[Head[tmp2]===Missing,AppendTo[errName,#];{-1},{tmp2}])&/@Join[data[[All,2]],data[[All,4]]];
		If[Length[errName]>0,Print["Error! line name : ",Length[errName]];Print[errName//Union];(*Quit[];*)];
		linePara=Join[tmp1[[;;nLine]],tmp1[[nLine+1;;]],busPara[[Flatten[tmp1[[;;nLine]]],{2}]],busPara[[Flatten[tmp1[[nLine+1;;]]],{2}]],data[[All,{11,6,7,9,12,13}]],2];
		tmp1=Select[data,Abs[#[[8]]]>10^-6&];If[Length[tmp1]>0,Print["Warning! Unhandle line G/2 : ",tmp1[[All,8]]];];
	];(* Line format:  numI numJ I J Ckt R X B Pmax Pmin *)

	(* T card: 
	1(1A1:T) (2A1:_/kxfm,P/axfm) (3A1) (4-6A3) 
	2(7-14A8:name1)
	3(15-18F4.0:kVbase1) 
	4(19I1) 
	5(20-27A8:name2)
	6(28-31F4.0:kVbase2) 
	7(32A1:Ckt) (34-37F4.0:Sn) (38I1) 
	89(39-50F6.5*2:R,X) 
	1011(51-62F6.5*2:G,B) 
	12(63-67F5.2:tap1/kV,angl/Degree) 
	13(68-72F5.2:tap2/kV) 
	14(75-77A1+I2) (78-80A1+I2) *)
	xfrmSep={7,15,19,20,28,32,39,45,51,57,63,68,75};
	tmp=Select[bpaData,StringStartsQ["T"]];nXfrm=tmp//Length;xfrmPara={};
	If[nXfrm>0,
		tmp3=Switch[StringTake[#,{2}]," ",1,"P",2,_,StringTake[#,2]]&/@tmp;
		tmp1=Position[tmp3,_?StringQ]//Flatten;
		If[Length[tmp1]>0,Print["Error! Unhandle type of xfrm : ",tmp3[[tmp1]]//Union];(*Quit[];*)
			tmp1=Complement[Range[nXfrm],tmp1];tmp=tmp[[tmp1]];tmp3=tmp3[[tmp1]];nXfrm=tmp//Length;];
		tmp1=StringInsert[(tmp2=StringLength[#];Which[tmp2<75,StringPadRight[#,75," "],tmp2>80,StringTake[#,{1,80}],True,#]),",",xfrmSep]&/@tmp;
		data=ImportString[Riffle[tmp1,Table["\n",{nXfrm}]]//StringJoin,{"CSV","RawData"}];data=Join[data,Table[{1,999,-999},{nXfrm}],2];If[chsChar>0,data[[All,2]]=chsCodeConvert[#]&/@data[[All,2]];data[[All,5]]=chsCodeConvert[#]&/@data[[All,5]];];
		tmp2=Join[{3,6},Range[8,13]];data[[All,tmp2]]=ToExpression[data[[All,tmp2]]/.{""->0,"."->0}];
		data[[All,8;;11]]=Map[If[#<100000,#,#/100000.]&,data[[All,8;;11]],{2}];
		data[[All,{12,13}]]=Map[If[-1000<#<10000,#,#/100.]&,data[[All,{12,13}]],{2}];
		data[[All,{12,13}]]=MapIndexed[If[tmp3[[First[#2]]]==1,{#1[[13]]*#1[[3]]/#1[[12]]/#1[[6]],0},{1,-#1[[12]]Degree}]&,data];
		errName={};tmp1=(tmp2=busPosAssoc[#];If[Head[tmp2]===Missing,AppendTo[errName,#];{-1},{tmp2}])&/@Join[data[[All,2]],data[[All,5]]];
		If[Length[errName]>0,Print["Error! xfrm name : ",Length[errName]];Print[errName//Union];(*Quit[];*)];
		xfrmPara=Join[tmp1[[nXfrm+1;;]],tmp1[[;;nXfrm]],busPara[[Flatten[tmp1[[nXfrm+1;;]]],{2}]],busPara[[Flatten[tmp1[[;;nXfrm]]],{2}]],data[[All,{15,8,9,12,13,15,15,15,15,15,15,15,10,11,15,16,17}]],2];
	];
	(* Xfrm format:  numI numJ I J Ckt R X Tk Ta Ttype Tmax Tmin Tap Ireg Cmax Cmin G B Name Pmax Pmin *)(* k:1+Z+GB *)

	If[optNodeLoc==1,tmp=tinney2ordering2[Join[If[nLine>0,linePara[[All,{1,2}]],{}],If[nXfrm>0,xfrmPara[[All,{1,2}]],{}]],nBus,info];
		busPara[[All,1]]=tmp[[busPara[[All,1]]]];genPara[[All,1]]=tmp[[genPara[[All,1]]]];
		If[nLoad>0,loadPara[[All,1]]=tmp[[loadPara[[All,1]]]];];
		If[nLine>0,linePara[[All,1]]=tmp[[linePara[[All,1]]]];linePara[[All,2]]=tmp[[linePara[[All,2]]]];];
		If[nXfrm>0,xfrmPara[[All,1]]=tmp[[xfrmPara[[All,1]]]];xfrmPara[[All,2]]=tmp[[xfrmPara[[All,2]]]];];
	];
	tmp=Sort[Transpose[{Range[nBus],busPara[[All,1]]}],#1[[2]]<#2[[2]]&];tmp1=tmp[[All,1]];
	(*Print[MatrixForm[{{"nBus",nBus},{"nLoad",nLoad},{"nGen",nGen},{"nLine",nLine},{"nXfrm",{nXfrm,{nXfrm2,nXfrm3}}}}]];
	Print[MatrixForm[busPara]];Print[MatrixForm[loadPara]];Print[MatrixForm[genPara]];Print[MatrixForm[linePara]];Print[MatrixForm[xfrmPara]];*)
	{busPara,loadPara,genPara,linePara,Select[xfrmPara,#[[9]]==0&],Select[xfrmPara,#[[9]]!=0&],{},{},tmp1,busPara[[tmp1,2]]}
	]



(************************************************************************************************)

formatUDF[bus_,brch_,gLmt_:{},gDyn_:{},gAux_:{},info_:5]:=Module[{name,num,num1,num2,num3,data,busPara,loadPara,genPara,linePara,xfrmPara,genDyn},
	name=bus[[All,1]];
	(* Bus format:  num I name type Vbase area GL BL V A Vmax Vmin *)
	num=Length[bus];num1=Range[num];num2=Table[0,{num}];num3=Table[1,{num}];
	busPara=Transpose[{num1,num1,bus[[All,1]],bus[[All,2]],num3,num2,num2,num2,bus[[All,7]],bus[[All,8]],1.1num3,0.9num3}];
	If[Length[bus[[1]]]==10,busPara[[All,{11,12}]]=bus[[All,{9,10}]];];
	(* Load format: num I ID PL QL IP IQ YP YQ *)
	data=Select[bus,#[[5]]!=0 || #[[6]]!=0&];
	num=Length[data];num1=Flatten[Position[name,#]&/@data[[All,1]]];num2=Table[1,{num}];num3=Table[0,{num}];
	loadPara=Transpose[{num1,num1,num2,data[[All,5]],data[[All,6]],num3,num3,num3,num3}];
	(* Gen format:  num I ID PG QG Vset Ireg Qmax Qmin Pmax Pmin a b c *)
	data=Select[bus,#[[3]]!=0 || #[[4]]!=0 || #[[2]]==2 || #[[2]]==3 &];
	num=Length[data];num1=Flatten[Position[name,#]&/@data[[All,1]]];num2=Table[1,{num}];num3=Table[0,{num}];
	genPara=Transpose[{num1,num1,num2,data[[All,3]],data[[All,4]],data[[All,7]],num3,999num2,-999num2,999num2,num3,num2,2num2,3num2}];
	If[Length[gLmt]>0,num=Intersection[busPara[[genPara[[All,1]],3]],gLmt[[All,1]]];
		num1=Flatten[Position[busPara[[genPara[[All,1]],3]],#]&/@num];num2=Flatten[Position[gLmt[[All,1]],#]&/@num];
		genPara[[num1,{8,9,10,11,12,13,14}]]=gLmt[[num2,{2,3,4,5,6,7,8}]];];
	(* Shunt compensator *)
	data=Select[brch,#[[1]]==#[[2]]&];
	num=Flatten[Position[name,#]&/@data[[All,1]]];
	busPara[[num,{7,8}]]=data[[All,{6,7}]];
	(* Line format:  numI numJ I J Ckt R X B Pmax Pmin *)
	data=Select[brch,#[[8]]==0 && #[[1]]!=#[[2]] &];num=Length[data];
	If[num==0,linePara={};,
		num1=Table[1,{num}];
		num2=Flatten[Position[name,#]&/@data[[All,1]]];
		num3=Flatten[Position[name,#]&/@data[[All,2]]];
		linePara=Transpose[{num2,num3,num2,num3,data[[All,3]],data[[All,4]],data[[All,5]],data[[All,7]],999num1,-999num1}];
		If[Length[data[[1]]]>13,linePara[[All,{9,10}]]=data[[All,{13,14}]];];];
	(* Xfrm format:  numI numJ I J Ckt R X Tk Ta Ttype Tmax Tmin Tap Ireg Cmax Cmin G B Name Pmax Pmin *)(* k:1+Z+GB *)
	data=Select[brch,#[[8]]!=0&];num=Length[data];
	If[num==0,xfrmPara={};,
		num1=Table[1,{num}];
		num2=Flatten[Position[name,#]&/@data[[All,1]]];
		num3=Flatten[Position[name,#]&/@data[[All,2]]];
		xfrmPara=Transpose[{num2,num3,num2,num3,data[[All,3]],data[[All,4]],data[[All,5]],data[[All,8]],Table[0,{num}],
			num1,1.1num1,0.9num1,33num1,num3,1.1num1,0.9num1,data[[All,6]],data[[All,7]],"Xfrm" num1,999num1,-999num1}];
		If[Length[data[[1]]]>8,xfrmPara[[All,9]]=data[[All,9]]*Degree;];
		If[Length[data[[1]]]>11,xfrmPara[[All,{11,12,13}]]=data[[All,{10,11,12}]];];
		If[Length[data[[1]]]>13,xfrmPara[[All,{20,21}]]=data[[All,{13,14}]];];];
	(* Gen Dyn & Aux *)
	If[Length[gDyn]==0,genDyn=gDyn;,num1=Flatten[Position[name,#]&/@gDyn[[All,1]]];num2=Partition[num1,1];genDyn=Join[num2,num2,gDyn,2];];

	(* Tinney2 node ordering *)
	If[optNodeLoc==1,num=tinney2ordering[Join[linePara[[All,{1,2}]],xfrmPara[[All,{1,2}]]],Length[busPara],info];
		busPara[[All,1]]=num[[busPara[[All,1]]]];
		loadPara[[All,1]]=num[[loadPara[[All,1]]]];genPara[[All,1]]=num[[genPara[[All,1]]]];
		linePara[[All,1]]=num[[linePara[[All,1]]]];linePara[[All,2]]=num[[linePara[[All,2]]]];
		xfrmPara[[All,1]]=num[[xfrmPara[[All,1]]]];xfrmPara[[All,2]]=num[[xfrmPara[[All,2]]]];
		If[Length[genDyn]>0,genDyn[[All,1]]=num[[genDyn[[All,1]]]];];
	];
	num=Sort[Transpose[{Range[Length[busPara]],busPara[[All,1]]}],#1[[2]]<#2[[2]]&];num1=num[[All,1]];
	num=Position[genPara[[All,8]]-genPara[[All,9]],x_/;x<10^-8]//Flatten;(* max=0<min : PV bus; max!=0<min : PQ bus *)
	(If[genPara[[#,8]]<10^-8,genPara[[#,8]]=999;genPara[[#,9]]=-999;busPara[[num1[[genPara[[#,1]]]],4]]=2;,busPara[[num1[[genPara[[#,1]]]],4]]=1;];)&/@num;
	If[Length[num]>0,Print["Reset unusual Gen ",num," state because Qmax-Qmin<=0."];];
	(*Print[MatrixForm[{{"nBus",nBus},{"nLoad",nLoad},{"nGen",nGen},{"nLine",nLine},{"nXfrm",{nXfrm,{nXfrm2,nXfrm3}}}}]];
	Print[MatrixForm[busPara]];Print[MatrixForm[loadPara]];Print[MatrixForm[genPara]];Print[MatrixForm[linePara]];Print[MatrixForm[xfrmPara]];*)
	{busPara,loadPara,genPara,linePara,Select[xfrmPara,#[[9]]==0&],Select[xfrmPara,#[[9]]!=0&],genDyn,gAux,num1,busPara[[num1,2]]}
	]



(************************************************************************************************)

caseSimpleSMSL[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["Simple Single-Machine-Single-Load System."];
	bus={
		{"bus-1", 3, 0.716, 0.27, 0.0,  0.0,  1.0,   0.0},
		{"bus-2", 1, 0.0,   0.0,  0.78, 0.40, 1.025, 9.3}};
		(* Bus  Type   Pg    Qg    Pl    Ql    V      A *)
	brch={
		{"bus-1", "bus-2", 1, 0.0, 0.2, 0.0, 0.0, 0.0}};
		(* From     To    Ckt  R    X   G/2  B/2   K *)
	gLmt={};
	gDyn={
		{"bus-1", 23.64, 0.1, 0.146, 0.0608, 0.0969, 0.0969, 8.96, 0.31, 1}};
		(* Bus     H      D     Xd     Xdt     Xq      Xqt   Td0t  Tq0t  Aux *)
	gAux={
		{0.0, 0.0, 0.0, 0.314, 1.0, 0.0039, 1.555, 0.35, 0.063, 0.2, 20.0, 10.0, 0.26, 0.5, 0.2, 0.05, 0.0}};
		(* Rs  Re   Xe   TE     KE   SEa     SEb    TF    KF    TA    KA    TRH   KHP  TCH  TSV   Rd   x1 *)
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseSimpleSMIB[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["Simple Single-Machine-Infinite-Bus System."];
	bus={
		{"bus-1", 2, 0.716, 0.27, 0.0,  0.0,  1.0,   0.0},
		{"bus-2", 3, 0.0,   0.0,  0.78, 0.40, 1.025, 9.3}};
		(* Bus  Type  Pg     Qg    Pl    Ql    V      A *)
	brch={
		{"bus-1", "bus-2", 1, 0.0, 0.2, 0.0, 0.0, 0.0}};
		(* From     To    Ckt  R    X   G/2  B/2   K *)
	gLmt={};
	gDyn={
		{"bus-1", 23.64,   0.1, 0.146, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1};
	    {"bus-2", 1233.64, 0.1, 0.146, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1}};
		(* Bus     H        D    Xd     Xdt      Xq     Xqt    Td0t  Tq0t  Aux *)
	gAux={
		{0.0, 0.0, 0.0, 0.314, 1.0, 0.0039, 1.555, 0.35, 0.063, 0.2, 20.0, 10.0, 0.26, 0.5, 0.2, 0.05, 0.0}};
		(* Rs  Re   Xe   TE     KE   SEa     SEb    TF    KF    TA    KA    TRH   KHP  TCH  TSV   Rd   x1 *)
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseChenH2g3b[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["ChenH2g3b 2-Gen-3-Bus System, p146"];(* ChenH2g3b, can be coupled *)
	bus={
		{"bus-1", 3, 0.0, 0.0, 0.0, 0.0, 1.00, 0.000000},
		{"bus-2", 1, 0.0, 0.0, 0.8, 0.6, 1.00, 21.84332},
		{"bus-3", 2, 0.4, 0.2, 0.0, 0.0, 1.10, 0.000000}};
		(* Bus  Type  Pg   Qg   Pl   Ql    V     A     *)
	brch={
		{"bus-1", "bus-2", 1, 0.0100200, 0.0400461, 0.0, 0.00, 0.0},
		{"bus-1", "bus-3", 1, 0.0496752, 0.1999750, 0.0, 0.33, 0.0}};
		(* From     To    Ckt    R          X       G/2   B/2   K *)
	gLmt={
		{"bus-1", 3.00, -3.0, 8.00, 1.00, 1200.6485, 200.4335, 50.4395},
		{"bus-3", 3.00, -3.0, 8.00, 1.00, 1857.2010, 500.7460, 200.550}};
		(* Bus    Qmax  Qmin  Pmax  Pmin    a0        a1        a2    *)
	gDyn={};
	gAux={};
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseXuWY3g5b[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["Wilsun Xu's 3-Gen 5-Bus System."];(* voltage reactive contribution *)
	bus={
		{"bus-1", 2, 1.00, 0.150, 0.0, 0.0, 1.05, 0.00},
		{"bus-2", 2, 0.25, 0.150, 0.0, 0.0, 1.05, 0.00},
		{"bus-3", 2, 0.25, 0.150, 0.0, 0.0, 1.05, 0.00},
		{"bus-4", 3, 0.00, 0.001, 0.0, 0.0, 1.00, 0.00},
		{"bus-5", 1, 0.00, 0.000, 1.5, 0.9, 1.00, 0.00}};
		(* Bus  Type  Pg    Qg     Pl   Ql   V     A  *)
	brch={
		{"bus-1", "bus-5", 1, 0.0, 0.1, 0.0, 0.0, 1.0},
		{"bus-2", "bus-5", 1, 0.0, 0.2, 0.0, 0.0, 1.0},
		{"bus-3", "bus-5", 1, 0.0, 0.3, 0.0, 0.0, 1.0},
		{"bus-4", "bus-5", 1, 0.0, 1.0, 0.0, 0.0, 1.0}};
		(* From     To    Ckt  R    X   G/2  B/2   K *)
	gLmt={
		{"bus-1", 3.00, -3.0, 8.00, 1.00, 1.0, 2.0, 5.0},
		{"bus-2", 3.00, -3.0, 8.00, 1.00, 1.0, 2.0, 5.0},
		{"bus-3", 3.00, -3.0, 8.00, 1.00, 1.0, 2.0, 5.0},
		{"bus-4", 3.00, -3.0, 8.00, 1.00, 1.0, 2.0, 5.0}};
		(* Bus    Qmax  Qmin  Pmax  Pmin  a0   a1   a2 *)
	gDyn={
		{"bus-1", 23.64, 1.1, 0.1460, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1},
		{"bus-2", 23.64, 2.1, 0.1460, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1},
		{"bus-3", 23.64, 1.1, 0.1460, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1},
		{"bus-4", 500.0, 2.1, 0.1460, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1}};
		(* Bus     H      D     Xd     Xdt     Xq      Xqt    Td0t  Tq0t  Aux *)
	gAux={
		{0.0, 0.0, 0.0, 0.314, 1.0, 0.0039, 1.555, 0.35, 0.063, 0.2, 20.0, 10.0, 0.26, 0.5, 0.2, 0.05, 0.0}};
		(* Rs  Re   Xe   TE     KE   SEa     SEb    TF    KF    TA    KA    TRH   KHP  TCH  TSV   Rd   x1 *)
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseWangXF2g5b[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["WangXF 2-Gen-5-Bus System, p74"];(* WangXF2g5b *)
	bus={
		{"bus-1", 1, 0.000, 0.0000, 1.60, 0.80, 0.86215, -4.77851, 1.10, 0.90},
		{"bus-2", 1, 0.000, 0.0000, 2.00, 1.00, 1.07791, 17.85353, 1.10, 0.90},
		{"bus-3", 1, 0.000, 0.0000, 3.70, 1.30, 1.03641, -4.28193, 1.10, 0.90},
		{"bus-4", 2, 5.000, 1.8000, 0.00, 0.00, 1.05000, 21.84332, 1.10, 0.90},
		{"bus-5", 3, 1.500, 2.4500, 0.00, 0.00, 1.05000, 0.000000, 1.10, 0.90}};
		(* Bus  Type  Pg     Qg      Pl    Ql     V        A       Vmax  Vmin *)
	brch={
		{"bus-1", "bus-2", 1, 0.0400, 0.2500, 0.0, 0.2500, 0.00, 0.0, 0.0, 0.0, 00, 2.00, -2.00},
		{"bus-1", "bus-3", 1, 0.1000, 0.3500, 0.0, 0.0000, 0.00, 0.0, 0.0, 0.0, 00, 0.65, -0.65},
		{"bus-2", "bus-3", 1, 0.0800, 0.3000, 0.0, 0.2500, 0.00, 0.0, 0.0, 0.0, 00, 2.00, -2.00},
		{"bus-2", "bus-4", 1, 0.0000, 0.0150, 0.0, 0.0000, 1.05, 0.0, 1.1, 0.9, 33, 6.00, -6.00},
		{"bus-3", "bus-5", 1, 0.0000, 0.0300, 0.0, 0.0000, 1.05, 0.0, 1.1, 0.9, 33, 5.00, -5.00}};
		(* From     To    Ckt   R       X     G/2   B/2     K     A   Kmax Kmin Tap Pmax  Pmin *)
	gLmt={
		{"bus-4", 3.00, -3.0, 8.00, 1.00, 1200.6485, 200.4335, 50.4395},
		{"bus-5", 5.00, -2.1, 8.00, 1.00, 1857.2010, 500.7460, 200.550}};
		(* Bus    Qmax  Qmin  Pmax  Pmin     a0        a1       a2    *)
	gDyn={};
	gAux={};
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseSauer3g9b[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["Sauer 3-Gen-9-Bus System, p171, p240 "];(* Sauer3g9b *)
	bus={
		{"bus-1", 3, 0.716, 0.2700, 0.00, 0.00, 1.040, 0.00},
		{"bus-2", 2, 1.630, 0.0670, 0.00, 0.00, 1.025, 9.30},
		{"bus-3", 2, 0.850, -0.109, 0.00, 0.00, 1.025, 4.70},
		{"bus-4", 1, 0.000, 0.0000, 0.00, 0.00, 1.026, -2.2},
		{"bus-5", 1, 0.000, 0.0000, 1.25, 0.50, 0.996, -4.0},
		{"bus-6", 1, 0.000, 0.0000, 0.90, 0.30, 1.013, -3.7},
		{"bus-7", 1, 0.000, 0.0000, 0.00, 0.00, 1.026, 3.70},
		{"bus-8", 1, 0.000, 0.0000, 1.00, 0.35, 1.016, 0.70},
		{"bus-9", 1, 0.000, 0.0000, 0.00, 0.00, 1.032, 2.00}};
		(* Bus  Type   Pg     Qg     Pl    Ql     V     A  *)
	brch={
		{"bus-1", "bus-4", 1, 0.0000, 0.0576, 0.0, 0.0000, 1.0},
		{"bus-2", "bus-7", 1, 0.0000, 0.0625, 0.0, 0.0000, 1.0},
		{"bus-3", "bus-9", 1, 0.0000, 0.0586, 0.0, 0.0000, 1.0},
		{"bus-4", "bus-5", 1, 0.0100, 0.0850, 0.0, 0.0880, 0.0},
		{"bus-4", "bus-6", 1, 0.0170, 0.0920, 0.0, 0.0790, 0.0},
		{"bus-5", "bus-7", 1, 0.0320, 0.1610, 0.0, 0.1530, 0.0},
		{"bus-6", "bus-9", 1, 0.0390, 0.1700, 0.0, 0.1790, 0.0},
		{"bus-7", "bus-8", 1, 0.0085, 0.0720, 0.0, 0.0745, 0.0},
		{"bus-8", "bus-9", 1, 0.0119, 0.1008, 0.0, 0.1045, 0.0}};
		(* From     To    Ckt   R       X     G/2   B/2     K *)
	gLmt={
		{"bus-1", 999., -99., 99.0, 0.00, 1200.6485, 200.4335, 50.4395},
		{"bus-2", 1.20, -0.3, 99.0, 0.00, 1200.6485, 200.4335, 50.4395},
		{"bus-3", 1.20, -0.3, 99.0, 0.00, 1857.2010, 500.7460, 200.550}};
		(* Bus    Qmax  Qmin  Pmax  Pmin     a0        a1       a2    *)
	gDyn={
		{"bus-1", 23.64, 0.1, 0.1460, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1},
		{"bus-2", 6.400, 0.2, 0.8958, 0.1198, 0.8645, 0.1969, 6.00, 0.535, 1},
		{"bus-3", 3.010, 0.3, 1.3125, 0.1813, 1.2578, 0.2500, 5.89, 0.600, 1}};
		(* Bus      H     D     Xd      Xdt     Xq      Xqt   Td0t  Tq0t  Aux *)
	gAux={
		{0.0, 0.0, 0.0, 0.314, 1.0, 0.0039, 1.555, 0.35, 0.063, 0.2, 20.0, 10.0, 0.26, 0.5, 0.2, 0.05, 0.0}};
		(* Rs  Re   Xe   TE     KE   SEa     SEb    TF    KF    TA    KA    TRH   KHP  TCH  TSV   Rd   x1 *)
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseTaylor10b[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["Taylor 3-Gen-10-bus system, p257 "];(* Taylor10b *)
	bus={
		{"bus-1" , 3, 35.561, 6.2328, 0.00, 0.00, 0.980000, 0.000000, 1.10, 0.90},
		{"bus-2" , 2, 15.000, 0.1740, 0.00, 0.00, 0.964000, -6.95677, 1.10, 0.90},
		{"bus-3" , 2, 10.940, 0.0032, 0.00, 0.00, 0.972000, -21.2184, 1.10, 0.90},
		{"bus-4" , 1, 0.0000, 0.0000, 0.00, 0.00, 1.095940, -3.92293, 1.10, 0.90},
		{"bus-5" , 1, 0.0000, 0.0000, 0.00, 0.00, 1.090020, -10.7616, 1.10, 0.90},
		{"bus-6" , 1, 0.0000, 0.0000, 0.00, 0.00, 1.079510, -25.0065, 1.10, 0.90},
		{"bus-7" , 1, 0.0000, 0.0000, 30.0, 18.0, 0.999031, -30.2673, 1.10, 0.90},
		{"bus-8" , 1, 0.0000, 0.0000, 0.00, 0.00, 1.012230, -30.2553, 1.10, 0.90},
		{"bus-9" , 1, 0.0000, 0.0000, 0.00, 0.00, 0.977771, -35.4805, 1.10, 0.90},
		{"bus-10", 1, 0.0000, 0.0000, 30.0, 0.00, 1.002640, -37.1043, 1.10, 0.90}};
		(* Bus   Type   Pg      Qg     Pl    Ql      V         A      Vmax  Vmin *)
	brch={
		{"bus-4" ,"bus-1" , 1, 0.0000, 0.001830, 0.0, 0.00000, 1.1291, 0.0, 1.0, 1.1, 33, 0.00, 0.00},
		{"bus-5" ,"bus-2" , 1, 0.0000, 0.004117, 0.0, 0.00000, 1.1291, 0.0, 1.0, 1.1, 33, 0.00, 0.00},
		{"bus-6" ,"bus-3" , 1, 0.0000, 0.005718, 0.0, 0.00000, 1.1082, 0.0, 1.0, 1.1, 33, 0.00, 0.00},
		{"bus-4" ,"bus-5" , 1, 0.0000, 0.004000, 0.0, 0.00000, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-5" ,"bus-6" , 1, 0.0015, 0.028800, 0.0, 1.17300, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-5" ,"bus-6" , 2, 0.0015, 0.028800, 0.0, 1.17300, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-5" ,"bus-6" , 3, 0.0015, 0.028800, 0.0, 1.17300, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-5" ,"bus-6" , 4, 0.0015, 0.028800, 0.0, 1.17300, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-5" ,"bus-6" , 5, 0.0015, 0.028800, 0.0, 1.17300, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-6" ,"bus-7" , 1, 0.0000, 0.003092, 0.0, 0.00000, 1.0660, 0.0, 1.0, 1.1, 33, 0.00, 0.00},
		{"bus-6" ,"bus-8" , 1, 0.0000, 0.003057, 0.0, 0.00000, 1.0600, 0.0, 1.0, 1.1, 33, 0.00, 0.00},
		{"bus-8" ,"bus-9" , 1, 0.0009, 0.003030, 0.0, 0.00000, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-9" ,"bus-10", 1, 0.0000, 0.000950, 0.0, 0.00000, 0.9748, 0.0, 1.0, 1.1, 33, 0.00, 0.00},
		{"bus-6" ,"bus-6" , 1, 0.0000, 0.000000, 0.0, 8.68000, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-7" ,"bus-7" , 1, 0.0000, 0.000000, 0.0, 15.0000, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00},
		{"bus-8" ,"bus-8" , 1, 0.0000, 0.000000, 0.0, 3.00000, 0.0000, 0.0, 0.0, 0.0, 00, 0.00, 0.00}};
		(* From     To     CKT   R        X      G/2    B/2     K       A   Kmax Kmin Tap Pmax  Pmin *)
	gLmt={
		{"bus-1", 100,  -100,  50.0, 1.00, 0.0, 200.0, 63.000},
		{"bus-2", 7.25, -2.0,  22.0, 1.00, 0.0, 175.0, 350.00},
		{"bus-3", 7.00, -2.0,  16.0, 1.00, 0.0, 100.0, 1250.0}};
		(* Bus    Qmax   Qmin  Pmax  Pmin   a0   a1     a2   *)
	gDyn={
		{"bus-1", 1000, 0.1, 0.1460, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1},
		{"bus-2", 2.32, 0.1, 0.1460, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1},
		{"bus-3", 2.32, 0.1, 0.1460, 0.0608, 0.0969, 0.0969, 8.96, 0.310, 1}};
		(* Bus     H     D     Xd     Xdt      Xq     Xqt    Td0t  Tq0t  Aux *)
	gAux={
		{0.0, 0.0, 0.0, 0.314, 1.0, 0.0039, 1.555, 0.35, 0.063, 0.2, 20.0, 10.0, 0.26, 0.5, 0.2, 0.05, 0.0}};
		(* Rs  Re   Xe   TE     KE   SEa     SEb    TF    KF    TA    KA    TRH   KHP  TCH  TSV   Rd   x1 *)
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseKundur4g2a[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["Kundur 4-Gen-2-Area System, p813 "];(* Kundur4g2a *)
	bus={
		{"bus-11", 2, 7.00, 1.85, 0.000, 0.0, 1.03, 27.00},
		{"bus-12", 2, 7.00, 2.35, 0.000, 0.0, 1.01, 17.30},
		{"bus-21", 3, 7.19, 1.76, 0.000, 0.0, 1.03, 0.000},
		{"bus-22", 2, 7.00, 2.02, 0.000, 0.0, 1.01, -10.2},
		{"bus-13", 1, 0.00, 0.00, 0.000, 0.0, 1.00, 0.000},
		{"bus-14", 1, 0.00, 0.00, 0.000, 0.0, 1.00, 0.000},
		{"bus-15", 1, 0.00, 0.00, 9.670, 1.0, 1.00, 0.000},
		{"bus-23", 1, 0.00, 0.00, 0.000, 0.0, 1.00, 0.000},
		{"bus-24", 1, 0.00, 0.00, 0.000, 0.0, 1.00, 0.000},
		{"bus-25", 1, 0.00, 0.00, 17.67, 1.0, 1.00, 0.000},
		{"bus-00", 1, 0.00, 0.00, 0.000, 0.0, 1.00, 0.000}};
		(* Bus   Type  Pg    Qg     Pl   Ql    V     A   *)
	brch={
		{"bus-11", "bus-13", 1, 0.000, 0.15/9, 0.0, 0.000000, 1.0},
		{"bus-12", "bus-14", 1, 0.000, 0.15/9, 0.0, 0.000000, 1.0},
		{"bus-21", "bus-23", 1, 0.000, 0.15/9, 0.0, 0.000000, 1.0},
		{"bus-22", "bus-24", 1, 0.000, 0.15/9, 0.0, 0.000000, 1.0},
		{"bus-13", "bus-14", 1, 0.0025 ,0.025, 0.0, 0.021875, 0.0},
		{"bus-14", "bus-15", 1, 0.0010 ,0.010, 0.0, 0.008750, 0.0},
		{"bus-15", "bus-00", 1, 0.0110 ,0.110, 0.0, 0.096250, 0.0},
		{"bus-15", "bus-00", 2, 0.0110 ,0.110, 0.0, 0.096250, 0.0},
		{"bus-23", "bus-24", 1, 0.0025 ,0.025, 0.0, 0.021875, 0.0},
		{"bus-24", "bus-25", 1, 0.0010 ,0.010, 0.0, 0.008750, 0.0},
		{"bus-25", "bus-00", 1, 0.0110 ,0.110, 0.0, 0.096250, 0.0},
		{"bus-25", "bus-00", 2, 0.0110 ,0.110, 0.0, 0.096250, 0.0},
		{"bus-15", "bus-15", 1, 0.0000 ,0.000, 0.0, 2.000000, 0.0},
		{"bus-25", "bus-25", 1, 0.0000 ,0.000, 0.0, 3.500000, 0.0}};
		(* From      To     Ckt   R      X     G/2    B/2      K *)
	gLmt={};
	gDyn={
		{"bus-11", 6.5009, 0.0, 1.8/9, 0.3/9, 1.7/9, 0.55/9, 8.0, 0.4, 1},
		{"bus-12", 6.5009, 0.0, 1.8/9, 0.3/9, 1.7/9, 0.55/9, 8.0, 0.4, 1},
		{"bus-21", 6.1759, 0.0, 1.8/9, 0.3/9, 1.7/9, 0.55/9, 8.0, 0.4, 1},
		{"bus-22", 6.1759, 0.0, 1.8/9, 0.3/9, 1.7/9, 0.55/9, 8.0, 0.4, 1}};
		(* Bus       H      D    Xd     Xdt    Xq     Xqt    Td0t Tq0t Aux *)
	gAux={
		{0.0025, 0.0, 0.0, 0.36, 1.0, 0.0056, 1.075, 1.8, 0.125, 0.055, 20.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0}};
		(* Rs     Re   Xe   TE    KE   SEa     SEb   TF    KF     TA     KA   TRH  KHP  TCH  TSV  Rd   x1 *)
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseSauer4g2a[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["Sauer 4-Gen-2-Area System, fast exciter, p278"];(* Sauer4g2a *)
	bus={
		{"bus-11", 2, 7.0000, 1.3386, 0.000, 0.00, 1.0300, 8.215400},
		{"bus-12", 2, 7.0000, 1.5920, 0.000, 0.00, 1.0100, -1.50400},
		{"bus-21", 3, 7.2172, 1.4466, 0.000, 0.00, 1.0300, 0.000000},
		{"bus-22", 2, 7.0000, 1.8083, 0.000, 0.00, 1.0100, -10.2051},
		{"bus-13", 1, 0.0000, 0.0000, 0.000, 0.00, 1.0108, 3.661500},
		{"bus-14", 1, 0.0000, 0.0000, 0.000, 0.00, 0.9875, -6.24330},
		{"bus-23", 1, 0.0000, 0.0000, 0.000, 0.00, 1.0095, -4.69770},
		{"bus-24", 1, 0.0000, 0.0000, 0.000, 0.00, 0.9850, -14.9443},
		{"bus-15", 1, 0.0000, 0.0000, 11.59, 2.12, 0.9761, -14.4194},
		{"bus-25", 1, 0.0000, 0.0000, 15.75, 2.88, 0.9716, -23.2922}};
		(* Bus   Type   Pg      Qg      Pl    Ql    V        A     *)
	brch={
		{"bus-11", "bus-13", 1, 0.001, 0.012, 0.0, 0.0000, 1.0},
		{"bus-12", "bus-14", 1, 0.001, 0.012, 0.0, 0.0000, 1.0},
		{"bus-13", "bus-14", 1, 0.005, 0.050, 0.0, 0.0375, 0.0},
		{"bus-13", "bus-14", 2, 0.005, 0.050, 0.0, 0.0375, 0.0},
		{"bus-14", "bus-15", 1, 0.002, 0.020, 0.0, 0.0150, 0.0},
		{"bus-14", "bus-15", 2, 0.002, 0.020, 0.0, 0.0150, 0.0},
		{"bus-15", "bus-25", 1, 0.022, 0.220, 0.0, 0.1650, 0.0},
		{"bus-15", "bus-25", 2, 0.022, 0.220, 0.0, 0.1650, 0.0},
		{"bus-15", "bus-25", 3, 0.022, 0.220, 0.0, 0.1650, 0.0},
		{"bus-21", "bus-23", 1, 0.001, 0.012, 0.0, 0.0000, 1.0},
		{"bus-22", "bus-24", 1, 0.001, 0.012, 0.0, 0.0000, 1.0},
		{"bus-23", "bus-24", 1, 0.005, 0.050, 0.0, 0.0375, 0.0},
		{"bus-23", "bus-24", 2, 0.005, 0.050, 0.0, 0.0375, 0.0},
		{"bus-24", "bus-25", 1, 0.002, 0.020, 0.0, 0.0150, 0.0},
		{"bus-24", "bus-25", 2, 0.002, 0.020, 0.0, 0.0150, 0.0},
		{"bus-15", "bus-15", 1, 0.000, 0.000, 0.0, 3.0000, 0.0},
		{"bus-25", "bus-25", 1, 0.000, 0.000, 0.0, 4.0000, 0.0}};
		(* From      To     Ckt   R      X    G/2   B/2     K *)
	gLmt={};
	gDyn={
		{"bus-11", 54.0, 0.0, 0.2, 0.033, 0.19, 0.061, 8.0, 0.4, 1},
		{"bus-12", 54.0, 0.0, 0.2, 0.033, 0.19, 0.061, 8.0, 0.4, 1},
		{"bus-21", 63.0, 0.0, 0.2, 0.033, 0.19, 0.061, 8.0, 0.4, 1},
		{"bus-22", 63.0, 0.0, 0.2, 0.033, 0.19, 0.061, 8.0, 0.4, 1}};
		(* Bus      H     D   Xd    Xdt    Xq    Xqt   Td0t Tq0t Aux *)
	gAux={
		{0.00028, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0001, 200.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.022}};
		(*  Rs    Re   Xe   TE   KE   SEa  SEb  TF   KF    TA      KA    TRH  KHP  TCH  TSV  Rd    x1  *)
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseIEEE14[info_:5]:=Module[{bus,brch,gLmt,gDyn,gAux},Print["IEEE 14-bus test system"];(* IEEE14 *)
	bus={
		{"bus-1",  3, 2.324, -0.165, 0.000, 0.0000, 1.06000, 0.000000, 1.06, 0.94},
		{"bus-2",  2, 0.400, 0.4356, 0.217, 0.1270, 1.04500, -4.98259, 1.06, 0.94},
		{"bus-3",  2, 0.000, 0.2508, 0.942, 0.1900, 1.01000, -12.7251, 1.06, 0.94},
		{"bus-4",  1, 0.000, 0.0000, 0.478, -0.039, 1.01767, -10.3129, 1.06, 0.94},
		{"bus-5",  1, 0.000, 0.0000, 0.076, 0.0160, 1.01951, -8.77385, 1.06, 0.94},
		{"bus-6",  2, 0.000, 0.1273, 0.112, 0.0750, 1.07000, -14.2209, 1.06, 0.94},
		{"bus-7",  1, 0.000, 0.0000, 0.000, 0.0000, 1.06152, -13.3596, 1.06, 0.94},
		{"bus-8",  2, 0.000, 0.1762, 0.000, 0.0000, 1.09000, -13.3596, 1.06, 0.94},
		{"bus-9",  1, 0.000, 0.0000, 0.295, 0.1660, 1.05593, -14.9385, 1.06, 0.94},
		{"bus-10", 1, 0.000, 0.0000, 0.090, 0.0580, 1.05098, -15.0973, 1.06, 0.94},
		{"bus-11", 1, 0.000, 0.0000, 0.035, 0.0180, 1.05691, -14.7906, 1.06, 0.94},
		{"bus-12", 1, 0.000, 0.0000, 0.061, 0.0160, 1.05519, -15.0756, 1.06, 0.94},
		{"bus-13", 1, 0.000, 0.0000, 0.135, 0.0580, 1.05038, -15.1563, 1.06, 0.94},
		{"bus-14", 1, 0.000, 0.0000, 0.149, 0.0500, 1.03553, -16.0336, 1.06, 0.94}};
		(* Bus   Type  Pg     Qg      Pl     Ql       V         A      Vmax  Vmin *)
	brch={
		{"bus-1",  "bus-2",  1, 0.01938, 0.05917, 0.00000, 0.0264, 0.000, 0.0, 0.0, 0.0, 00, 3.42, -3.42},
		{"bus-1",  "bus-5",  1, 0.05403, 0.22304, 0.00000, 0.0246, 0.000, 0.0, 0.0, 0.0, 00, 1.71, -1.71},
		{"bus-2",  "bus-3",  1, 0.04699, 0.19797, 0.00000, 0.0219, 0.000, 0.0, 0.0, 0.0, 00, 1.71, -1.71},
		{"bus-2",  "bus-4",  1, 0.05811, 0.17632, 0.00000, 0.0170, 0.000, 0.0, 0.0, 0.0, 00, 1.71, -1.71},
		{"bus-2",  "bus-5",  1, 0.05695, 0.17388, 0.00000, 0.0173, 0.000, 0.0, 0.0, 0.0, 00, 1.71, -1.71},
		{"bus-3",  "bus-4",  1, 0.06701, 0.17103, 0.00000, 0.0064, 0.000, 0.0, 0.0, 0.0, 00, 1.71, -1.71},
		{"bus-4",  "bus-5",  1, 0.01335, 0.04211, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 1.71, -1.71},
		{"bus-6",  "bus-11", 1, 0.09498, 0.19890, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-6",  "bus-12", 1, 0.12291, 0.25581, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-6",  "bus-13", 1, 0.06615, 0.13027, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-7",  "bus-8",  1, 0.00000, 0.17615, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-7",  "bus-9",  1, 0.00000, 0.11001, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.65, -0.65},
		{"bus-9",  "bus-10", 1, 0.03181, 0.08450, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-9",  "bus-14", 1, 0.12711, 0.27038, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-10", "bus-11", 1, 0.08205, 0.19207, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-12", "bus-13", 1, 0.22092, 0.19988, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-13", "bus-14", 1, 0.17093, 0.34802, 0.00000, 0.0000, 0.000, 0.0, 0.0, 0.0, 00, 0.50, -0.50},
		{"bus-4",  "bus-7",  1, 0.00000, 0.20912, 0.00000, 0.0000, 0.978, 0.0, 1.1, 0.9, 33, 0.65, -0.65},
		{"bus-4",  "bus-9",  1, 0.00000, 0.55618, 0.00000, 0.0000, 0.969, 0.0, 1.1, 0.9, 33, 0.40, -0.40},
		{"bus-5",  "bus-6",  1, 0.00000, 0.25202, 0.00000, 0.0000, 0.932, 0.0, 1.1, 0.9, 33, 0.65, -0.65},
		{"bus-9",  "bus-9",  1, 0.00000, 0.00000, 0.00000, 0.1900, 0.000, 0.0, 0.0, 0.0, 00, 0.00, -0.00}};
		(* From      To     CKT    R        X      G/2      B/2     K      A   Kmax Kmin Tap Pmax   Pmin *)
	gLmt={
		{"bus-1", 1.00, -0.30, 3.324, 0.00, 0.0, 200.0, 63.000},
		{"bus-2", 0.50, -0.40, 1.400, 0.00, 0.0, 175.0, 350.00},
		{"bus-3", 0.40, 0.000, 1.000, 0.00, 0.0, 100.0, 1250.0},
		{"bus-6", 0.24, -0.06, 1.000, 0.00, 0.0, 325.0, 166.80},
		{"bus-8", 0.24, -0.06, 1.000, 0.00, 0.0, 300.0, 500.00}};
		(* Bus    Qmax   Qmin   Pmax   Pmin  a0   a1     a2   *)
	gDyn={};
	gAux={};
	formatUDF[bus,brch,gLmt,gDyn,gAux,info]
	]

(************************************************************************************************)

caseData[name_,optNode_:1,info_:5]:=Module[{out},optNodeLoc=optNode;
	If[info>7,If[optNode!=1,Print["Bus node is not re-numbered."];,Print["Bus node is re-numbered based on Tinney 2 schema."];];];
	Which[
		name=="SimpleSMSL",out=caseSimpleSMSL[info];,
		name=="SimpleSMIB",out=caseSimpleSMIB[info];,
		name=="ChenH2g3b",out=caseChenH2g3b[info];,
		name=="XuWY3g5b",out=caseXuWY3g5b[info];,
		name=="WangXF2g5b",out=caseWangXF2g5b[info];,
		name=="Sauer3g9b",out=caseSauer3g9b[info];,
		name=="Taylor10b",out=caseTaylor10b[info];,
		name=="Kundur4g2a",out=caseKundur4g2a[info];,
		name=="Sauer4g2a",out=caseSauer4g2a[info];,
		name=="IEEE14",out=caseIEEE14[info];,
		True,
			If[!FileExistsQ[name],Input[name<>" not exist! Quit."];Quit[];];
			Which[StringContainsQ[name,".raw",IgnoreCase->True],out=casePSSE30[name,info];,
				StringContainsQ[name,".m",IgnoreCase->True],out=caseMpc2[name,info];,
				StringContainsQ[name,".dat",IgnoreCase->True],out=caseBpa43[name,info];,
				True,Input[name<>" unknown data file! Quit."];Quit[];
			];
		];
	Chop[out]
	]

End[]

EndPackage[]
