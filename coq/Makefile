CC=coqc
CFLAGS=

all: SystemFC SystemFCProp

SystemFCProp: SystemFCProp.v SystemFC
	$(CC) $(CFLAGS) SubstProp.v
	$(CC) $(CFLAGS) SystemFCProp.v

SystemFC: SystemFC.v SfLib
	$(CC) $(CFLAGS) SystemFC.v
	$(CC) $(CFLAGS) Shifting.v
	$(CC) $(CFLAGS) Substitution.v
	$(CC) $(CFLAGS) Typing.v
	$(CC) $(CFLAGS) Evaluation.v

SfLib: SfLib.v
	$(CC) $(CFLAGS) SfLib.v

clean:
	rm *.vo *.glob
