function toggleDisplay(id)
{
   $(document.getElementById(id)).toggleClass('hidden');
}

function hideAll(cls)
{
  $('div.' + cls).addClass('hidden');
}

$(document).ready(function () {
    hideAll('proofscript');
});

