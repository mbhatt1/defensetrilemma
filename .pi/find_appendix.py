import pypdf
p = pypdf.PdfReader('/Users/mbhatt/stuff/paper2_neurips.pdf')
print('total pages:', len(p.pages))
for i, page in enumerate(p.pages):
    text = page.extract_text() or ''
    head = text[:200].replace('\n', ' ')
    mark = ''
    if 'ppendix' in text[:200] or 'Supplementary' in text[:200]:
        mark = ' <-- APPENDIX-LIKE'
    print(f'page {i+1}: {head[:160]}{mark}')
