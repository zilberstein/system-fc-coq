CC=coqc
CFLAGS=

all: SystemF SystemFProp

SystemFProp: SystemFProp.v SystemF
	$(CC) $(CFLAGS) SystemFProp.v

SystemF: SystemF.v SfLib
	$(CC) $(CFLAGS) SystemF.v

SfLib: SfLib.v
	$(CC) $(CFLAGS) SfLib.v

clean:
	rm *.vo *.glob
