CC=coqc
CFLAGS=

all: SystemF SystemFProp

SystemFProp: SystemFProp.v SystemF
	$(CC) $(CFLAGS) SystemFProp.v

SystemF: SystemF.v SfLib
	$(CC) $(CFLAGS) SystemF.v

Types: Types.v Smallstep
	$(CC) $(CFLAGS) Types.v

Smallstep: Smallstep.v Imp
	$(CC) $(CFLAGS) Smallstep.v

Imp: Imp.v SfLib
	$(CC) $(CFLAGS) Imp.v

SfLib: SfLib.v
	$(CC) $(CFLAGS) SfLib.v

clean:
	rm *.vo *.glob
