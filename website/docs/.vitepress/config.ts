import { defineConfig } from 'vitepress'

export default defineConfig({
  title: 'The Defense Trilemma',
  description:
    'A diagrammatic walkthrough of the impossibility of continuous, utility-preserving wrapper defenses on connected spaces.',
  cleanUrls: true,
  lang: 'en-US',

  head: [
    [
      'link',
      {
        rel: 'stylesheet',
        href: 'https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css',
        integrity:
          'sha384-nB0miv6/jRmo5UMMR1wu3Gz6NLsoTkbqJghGIsx//Rlm+ZU03BU6SQNC66uf4l5+',
        crossorigin: ''
      }
    ]
  ],

  markdown: {
    math: true,
    theme: {
      light: 'github-light',
      dark: 'github-dark'
    },
    lineNumbers: false
  },

  themeConfig: {
    siteTitle: 'Defense Trilemma',
    nav: [
      { text: 'Paper', link: 'https://github.com/mbhatt1/stuff/blob/main/paper2_neurips.pdf' },
      { text: 'Lean Artifact', link: 'https://github.com/mbhatt1/stuff/tree/main/ManifoldProofs' },
      { text: 'GitHub', link: 'https://github.com/mbhatt1/stuff' }
    ],
    sidebar: [
      {
        text: 'Overview',
        items: [
          { text: 'The Trilemma', link: '/' },
          { text: '2D Prompt Space', link: '/prompt-space' }
        ]
      },
      {
        text: 'Theory',
        items: [
          { text: 'Boundary Fixation Proof', link: '/boundary-proof' },
          { text: 'Three-Level Hierarchy', link: '/hierarchy' },
          { text: 'The K Dilemma', link: '/dilemma' },
          { text: 'Discrete Dilemma', link: '/discrete' },
          { text: 'Extensions', link: '/extensions' }
        ]
      },
      {
        text: 'Validation & Practice',
        items: [
          { text: 'Empirical Surfaces', link: '/empirical' },
          { text: 'Counterexamples', link: '/counterexamples' },
          { text: 'Engineering Prescription', link: '/engineering' }
        ]
      },
      {
        text: 'Formalization',
        items: [
          { text: 'Lean Artifact Map', link: '/lean-artifact' }
        ]
      }
    ],
    socialLinks: [
      { icon: 'github', link: 'https://github.com/mbhatt1/stuff' }
    ],
    footer: {
      message:
        'Bhatt, Munshi, Narajala, Habler, Al-Kahfah, Huang, Gatto. Mechanically verified in Lean 4 + Mathlib.',
      copyright: 'CC BY 4.0'
    },
    search: { provider: 'local' },
    outline: { level: [2, 3] }
  }
})
