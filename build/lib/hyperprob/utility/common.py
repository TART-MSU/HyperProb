from termcolor import colored


def colourerror(text):
    text = colored("\n" + text + "\n", 'red')
    print(text)


def colourinfo(text):
    text = colored("\n" + text + "\n", 'yellow')
    print(text)


def colouroutput(text):
    text = colored("\n" + text + "\n", 'green')
    print(text)


def colourother(text):
    text = colored("\n" + text + "\n", 'blue')
    print(text)
