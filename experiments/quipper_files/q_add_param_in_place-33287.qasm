OPENQASM 2.0;
include "qelib1.inc";

qreg in[16];
x in[15];
qreg anc16[1];
x in[15];
cx in[15],anc16[0];
x in[15];
x in[14];
cx anc16[0],in[14];
qreg anc17[1];
x in[14];
cx in[14],anc17[0];
x in[14];
cx anc16[0],anc17[0];
x in[14];
ccx in[14],anc16[0],anc17[0];
x in[14];
x in[13];
cx anc17[0],in[13];
qreg anc18[1];
x in[13];
cx in[13],anc18[0];
x in[13];
cx anc17[0],anc18[0];
x in[13];
ccx in[13],anc17[0],anc18[0];
x in[13];
cx anc18[0],in[12];
qreg anc19[1];
x in[12];
ccx in[12],anc18[0],anc19[0];
x in[12];
cx anc19[0],in[11];
qreg anc20[1];
x in[11];
ccx in[11],anc19[0],anc20[0];
x in[11];
cx anc20[0],in[10];
qreg anc21[1];
x in[10];
ccx in[10],anc20[0],anc21[0];
x in[10];
cx anc21[0],in[9];
qreg anc22[1];
x in[9];
ccx in[9],anc21[0],anc22[0];
x in[9];
cx anc22[0],in[8];
qreg anc23[1];
x in[8];
ccx in[8],anc22[0],anc23[0];
x in[8];
cx anc23[0],in[7];
qreg anc24[1];
x in[7];
ccx in[7],anc23[0],anc24[0];
x in[7];
x in[6];
cx anc24[0],in[6];
qreg anc25[1];
x in[6];
cx in[6],anc25[0];
x in[6];
cx anc24[0],anc25[0];
x in[6];
ccx in[6],anc24[0],anc25[0];
x in[6];
cx anc25[0],in[5];
qreg anc26[1];
x in[5];
ccx in[5],anc25[0],anc26[0];
x in[5];
cx anc26[0],in[4];
qreg anc27[1];
x in[4];
ccx in[4],anc26[0],anc27[0];
x in[4];
cx anc27[0],in[3];
qreg anc28[1];
x in[3];
ccx in[3],anc27[0],anc28[0];
x in[3];
cx anc28[0],in[2];
qreg anc29[1];
x in[2];
ccx in[2],anc28[0],anc29[0];
x in[2];
cx anc29[0],in[1];
qreg anc30[1];
x in[1];
ccx in[1],anc29[0],anc30[0];
x in[1];
x in[0];
cx anc30[0],in[0];
x in[1];
ccx in[1],anc29[0],anc30[0];
x in[1];
reset anc30[0];
x in[2];
ccx in[2],anc28[0],anc29[0];
x in[2];
reset anc29[0];
x in[3];
ccx in[3],anc27[0],anc28[0];
x in[3];
reset anc28[0];
x in[4];
ccx in[4],anc26[0],anc27[0];
x in[4];
reset anc27[0];
x in[5];
ccx in[5],anc25[0],anc26[0];
x in[5];
reset anc26[0];
x in[6];
ccx in[6],anc24[0],anc25[0];
x in[6];
cx anc24[0],anc25[0];
x in[6];
cx in[6],anc25[0];
x in[6];
reset anc25[0];
x in[7];
ccx in[7],anc23[0],anc24[0];
x in[7];
reset anc24[0];
x in[8];
ccx in[8],anc22[0],anc23[0];
x in[8];
reset anc23[0];
x in[9];
ccx in[9],anc21[0],anc22[0];
x in[9];
reset anc22[0];
x in[10];
ccx in[10],anc20[0],anc21[0];
x in[10];
reset anc21[0];
x in[11];
ccx in[11],anc19[0],anc20[0];
x in[11];
reset anc20[0];
x in[12];
ccx in[12],anc18[0],anc19[0];
x in[12];
reset anc19[0];
x in[13];
ccx in[13],anc17[0],anc18[0];
x in[13];
cx anc17[0],anc18[0];
x in[13];
cx in[13],anc18[0];
x in[13];
reset anc18[0];
x in[14];
ccx in[14],anc16[0],anc17[0];
x in[14];
cx anc16[0],anc17[0];
x in[14];
cx in[14],anc17[0];
x in[14];
reset anc17[0];
x in[15];
cx in[15],anc16[0];
x in[15];
reset anc16[0];

