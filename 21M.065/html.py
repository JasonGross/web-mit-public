def ampersand_encode(text):
    return ''.join((i if ord(i) < 127
                    else '&#%d;' % ord(i))
                   for i in text)
