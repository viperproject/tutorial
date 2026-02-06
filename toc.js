// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded "><a href="introduction.html"><strong aria-hidden="true">1.</strong> Introduction</a></li><li class="chapter-item expanded "><a href="structure.html"><strong aria-hidden="true">2.</strong> Structure</a></li><li class="chapter-item expanded "><a href="language.html"><strong aria-hidden="true">3.</strong> Language Overview</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="language-top.html"><strong aria-hidden="true">3.1.</strong> Top-level declarations</a></li><li class="chapter-item expanded "><a href="language-types.html"><strong aria-hidden="true">3.2.</strong> Built-in types</a></li><li class="chapter-item expanded "><a href="language-imports.html"><strong aria-hidden="true">3.3.</strong> Imports</a></li></ol></li><li class="chapter-item expanded "><a href="permissions.html"><strong aria-hidden="true">4.</strong> Permissions</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="permissions-state.html"><strong aria-hidden="true">4.1.</strong> Viper&#39;s program state</a></li><li class="chapter-item expanded "><a href="permissions-inhale-exhale.html"><strong aria-hidden="true">4.2.</strong> Inhaling and exhaling</a></li><li class="chapter-item expanded "><a href="permissions-self-framing.html"><strong aria-hidden="true">4.3.</strong> Self-framing assertions</a></li><li class="chapter-item expanded "><a href="permissions-exclusive.html"><strong aria-hidden="true">4.4.</strong> Exclusive permissions</a></li><li class="chapter-item expanded "><a href="permissions-fractional.html"><strong aria-hidden="true">4.5.</strong> Fractional permissions</a></li></ol></li><li class="chapter-item expanded "><a href="predicates.html"><strong aria-hidden="true">5.</strong> Predicates</a></li><li class="chapter-item expanded "><a href="functions.html"><strong aria-hidden="true">6.</strong> Functions</a></li><li class="chapter-item expanded "><a href="quantifiers.html"><strong aria-hidden="true">7.</strong> Quantifiers</a></li><li class="chapter-item expanded "><a href="quantified-permissions.html"><strong aria-hidden="true">8.</strong> Quantified Permissions</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="quantified-permissions-injectivity.html"><strong aria-hidden="true">8.1.</strong> Receiver expressions and injectivity</a></li></ol></li><li class="chapter-item expanded "><a href="magic-wands.html"><strong aria-hidden="true">9.</strong> Magic Wands</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="magic-wands-package.html"><strong aria-hidden="true">9.1.</strong> Package operations</a></li><li class="chapter-item expanded "><a href="magic-wands-heap-dependent.html"><strong aria-hidden="true">9.2.</strong> Heap-dependent expressions</a></li></ol></li><li class="chapter-item expanded "><a href="statements.html"><strong aria-hidden="true">10.</strong> Statements</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="statements-assignments.html"><strong aria-hidden="true">10.1.</strong> Assignments</a></li><li class="chapter-item expanded "><a href="statements-control.html"><strong aria-hidden="true">10.2.</strong> Control structures</a></li><li class="chapter-item expanded "><a href="statements-assertions.html"><strong aria-hidden="true">10.3.</strong> Assertion checking</a></li><li class="chapter-item expanded "><a href="statements-verifier.html"><strong aria-hidden="true">10.4.</strong> Verifier directives</a></li></ol></li><li class="chapter-item expanded "><a href="expressions.html"><strong aria-hidden="true">11.</strong> Expressions</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="expressions-integer.html"><strong aria-hidden="true">11.1.</strong> Integer expressions</a></li><li class="chapter-item expanded "><a href="expressions-boolean.html"><strong aria-hidden="true">11.2.</strong> Boolean expressions</a></li><li class="chapter-item expanded "><a href="expressions-reference.html"><strong aria-hidden="true">11.3.</strong> Reference expressions</a></li><li class="chapter-item expanded "><a href="expressions-perm.html"><strong aria-hidden="true">11.4.</strong> Perm expressions</a></li><li class="chapter-item expanded "><a href="expressions-sequence.html"><strong aria-hidden="true">11.5.</strong> Sequence expressions</a></li><li class="chapter-item expanded "><a href="expressions-set-multiset.html"><strong aria-hidden="true">11.6.</strong> Set and multiset expressions</a></li><li class="chapter-item expanded "><a href="expressions-map.html"><strong aria-hidden="true">11.7.</strong> Map expressions</a></li><li class="chapter-item expanded "><a href="expressions-multi.html"><strong aria-hidden="true">11.8.</strong> Expressions of multiple types</a></li></ol></li><li class="chapter-item expanded "><a href="assertions.html"><strong aria-hidden="true">12.</strong> Assertions</a></li><li class="chapter-item expanded "><a href="domains.html"><strong aria-hidden="true">13.</strong> Domains</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="domains-new-types.html"><strong aria-hidden="true">13.1.</strong> Declaring new types</a></li><li class="chapter-item expanded "><a href="domains-axiomatising.html"><strong aria-hidden="true">13.2.</strong> Axiomatising custom theories</a></li><li class="chapter-item expanded "><a href="domains-array.html"><strong aria-hidden="true">13.3.</strong> Encoding an array datatype</a></li><li class="chapter-item expanded "><a href="domains-adt.html"><strong aria-hidden="true">13.4.</strong> ADT plugin</a></li></ol></li><li class="chapter-item expanded "><a href="termination.html"><strong aria-hidden="true">14.</strong> Termination</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="termination-measures.html"><strong aria-hidden="true">14.1.</strong> Termination measures and decreases clauses</a></li><li class="chapter-item expanded "><a href="termination-syntax.html"><strong aria-hidden="true">14.2.</strong> General syntax of decreases tuples</a></li><li class="chapter-item expanded "><a href="termination-special-tuples.html"><strong aria-hidden="true">14.3.</strong> Special decreases tuples</a></li><li class="chapter-item expanded "><a href="termination-custom-orders.html"><strong aria-hidden="true">14.4.</strong> Custom well-founded orders</a></li><li class="chapter-item expanded "><a href="termination-mutual-recursion.html"><strong aria-hidden="true">14.5.</strong> Mutual recursion</a></li><li class="chapter-item expanded "><a href="termination-conditional.html"><strong aria-hidden="true">14.6.</strong> Conditional termination</a></li><li class="chapter-item expanded "><a href="termination-abstract.html"><strong aria-hidden="true">14.7.</strong> Abstract functions</a></li><li class="chapter-item expanded "><a href="termination-statement.html"><strong aria-hidden="true">14.8.</strong> Statement termination (experimental)</a></li></ol></li><li class="chapter-item expanded "><a href="further-info.html"><strong aria-hidden="true">15.</strong> Further Information</a></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split("#")[0].split("?")[0];
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
