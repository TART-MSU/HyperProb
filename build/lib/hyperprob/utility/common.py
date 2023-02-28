from termcolor import colored


def colourerror(text, newline=True):
    if newline:
        text = colored("\n" + text, 'red')
    else:
        text = colored(text, 'red')
    print(text)


def colourinfo(text, newline=True):
    if newline:
        text = colored("\n" + text, 'yellow')
    else:
        text = colored(text, 'yellow')
    print(text)


def colouroutput(text, newline=True):
    if newline:
        text = colored("\n" + text, 'green')
    else:
        text = colored(text, 'green')
    print(text)


def colourother(text, newline=True):
    if newline:
        text = colored("\n" + text, 'blue')
    else:
        text = colored(text, 'blue')
    print(text)
